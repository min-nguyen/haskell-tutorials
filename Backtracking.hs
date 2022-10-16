{- https://okmij.org/ftp/Computation/LogicT.pdf
-}

{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import Control.Monad.Trans
import Control.Monad.Identity (Identity)
import Data.Functor.Identity

{- The MonadPlus interface provides two primitives for expressing backtracking computations
-}
class Monad m => MonadPlus m where
  -- | Failure
  mzero :: m a
  -- | A choice junction, representing a *disjunction* of goals
  mplus :: m a -> m a -> m a

{- MonadPlus laws

  # identity
  a `mplus` mzero = a
  mzero `mplus` a = a

  # associativity
  a `mplus` (b `mplus` c) = (a `muplus` b) `mplus` c

  # distributivity: bind represents a *conjunction* of goals
  mzero >>= k = mzero
  a `mplus` b >>= k = (a >>= k) `mplus (b >>= k)
-}

-- | The list monad is a straightforward example of the MonadPlus interface.
instance MonadPlus [] where
  mzero :: [a]
  mzero = []
  mplus :: [a] -> [a] -> [a]
  mplus = (++)

-- | A list computation representing multiple choice can be converted to a stream of answers with the identity function.
runList :: [a] -> [a]
runList = id

{- 3. A More Expressive Interface

   The list monad has an interpretive overhead because it constructs and destructs singleton lists over and over again.
   It also takes quadratic time to enumerate all the solutions of a program.
   Below we aim generalise the runList function to monads m other than the list monad.

   runN :: Maybe Int -> m a -> [a]
-}

{- 3.2 Fair disjunction

  Many logic programs make a potentially infinite number of non-deterministic choices

  odds :: MonadPlus m => m Int
  odds = pure 1 `mplus` (odds >>= \a -> pure (2 + a))
   which expands into:
       = pure 1 `mplus` (pure 1 `mplus` (odds >>= \b -> pure (2 + b)) >>= \a -> pure (2 + a))
   which due to the definition of bind, then expands into:
       = pure 1 `mplus` ((pure 1 >>= \a -> pure (2 + a)) `mplus` (odds >>= \b -> pure (2 + b) >>= \a -> pure (2 + a)) )

  Computations that succeed an infinite number of times cannot be combined naively with other computations.

    m_1 `mplus` m_2 = m_1      when m_1 can backtrack arbitrarily many times.

  For example, the following computation diverges on `odds` without ever considering `evens`.

  runN (Just 1) (do x <- odds `mplus` evens
                    if even x then pure x else mzero)

  We therefore would like a primitive "interleave" that allows for *fair disjunction*,
  such that answers produced by one computation can be interleaved with answers from another.

  runN (Just 1) (do x <- odds `interleave` evens
                  if even x then pure x else mzero)
-}

{- 3.3 Fair Conjunction

  In the following distributivity law:

    a `mplus` b >>= k    =     (a >>= k) `mplus` (b >>= k)

  If a >>= k can backtrack arbitrarily many times, then:

    a `mplus` b >>= k    =     a >>= k

  For example, the following computation diverges on `pure 0 >>= oddsPlus` even though `pure 1 >>= oddsPlus` is successful.

  oddsPlus :: MonadPlus m => Int -> m Int
  oddsPlus n = odds >>= \a -> pure (a + n)

  runN (Just 1) (do x <- (pure 0 `mplus` pure 1) >>= oddsPlus
                    if even x then pure x else mzero)

  We therefore would like a primitive ">>-" that allows for *fair conjunction*,

  runN (Just 1) (do x <- (pure 0 `mplus` pure 1) >>- oddsPlus
                    if even x then pure x else mzero)
-}

{- 3.5 Soft cut

  In Haskell, one can use ordinary conditionals to restrict the conditions that non-deterministic computations can succeed:

  guard :: (MonadPlus m) => Bool -> m ()
  guard True  = return ()
  guard False = mzero

  For example, the following computation restricts odd numbers `n` to those that are divisible by another number `d`.

  runN (Just 10) (do n <- odds
                     guard (n > 1)                        -- | if this returns `mzero`, then `mzero >>= k` = `mzero` applies.
                     d <- msum (map pure [1 .. n - 1])
                     guard (d > 1 && n `mod` d == 0)
                     pure n)

  However, we can not restrict the computation by filtering odd numbers `n` that are *not* divisible any other number `d`.

  We would therefore like another primitive "ifte", where:

    ifte t th el

  performs `th` if `t` succeeds and `el` otherwise.

  runN (Just 10) (do n <- odds
                     guard (n > 1)
                     ifte (do d <- msum (map pure [1 .. n - 1])
                              guard (d > 1 && n `mod` d == 0))
                          (const mzero)
                          (pure n))
-}

{- 3.6 Pruning

   In addition to `ifte`, which is a pruning primitive, another important pruning primitive is `once` which selects
   one solution out of possibly many to avoid wasteful backtracking.

   For example, if a prime number `n` is divisible by any number `d`, there is no need to look for further factorisations:

   runN (Just 10) (do n <- odds
                     guard (n > 1)
                     ifte (once (do d <- msum (map pure [1 .. n - 1])
                                    guard (d > 1 && n `mod` d == 0)))
                          (const mzero)
                          (pure n))
-}

{- 4. Splitting Computations

   The class LogicM extends the MonadPlus interface with the previously introduced primitives.
   It turns out that all these primitives can be implemented with one new abstraction: msplit.
-}

class MonadPlus m => LogicM m where
  {- The function `msplit` takes a computation and determines if that computation fails by returning Nothing,
     or succeeds at least once by returning the first result and the rest of the computation.
     Its laws are:
        msplit mzero              = pure Nothing
        msplit (pure a `mplus` m) = pure (Just (a, m))
  -}
  msplit :: m a -> m (Maybe (a, m a))

  -- | Fair disjunction
  interleave :: m a -> m a -> m a
  interleave p1 p2 = do
    -- Run the first computation up to its first result
    r <- msplit p1
    case r of
      -- If it fails, perform the entire second computation
      Nothing -> p2
      -- If it succeeds, return the result, and perform the second computation interleaved with the rest of the first computation
      Just (r1, p1') -> pure r1 `mplus` interleave p2 p1'

  -- | Fair conjunction
  (>>-) :: m a -> (a -> m b) -> m b
  p >>- k = do
    -- Run the computation to its first result
    r <- msplit p
    case r of
      Nothing -> mzero
      -- Perform the continuation on the first result, and interleave its results with
      -- the continuation fairly applied to the rest of the computation branches
      Just (r, p') -> interleave (k r) (p' >>- k)

  -- | Soft cutting
  ifte :: m a -> (a -> m b) -> m b -> m b
  ifte t th el = do
    r <- msplit t
    case r of
      Nothing      -> el
      -- If at least one result is returned, then execute the `then` branch on all of the results.
      Just (r1, p) -> th r1 `mplus` (p >>= th)

  -- | Pruning
  once :: m a -> m a
  once m = do
    r <- msplit m
    case r of
      Nothing      -> mzero
      -- Return the first result, ignore the rest of the computation
      Just (r1, _) -> pure r1

{- The implementation of LogicM for List is straightforward. -}
instance LogicM [] where
  msplit :: [a] -> [Maybe (a, [a])]
  msplit []     = pure Nothing
  msplit (x:xs) = pure (Just (x, xs))

{- 5. LogicT

  Rather than working with `LogicM`, we would like to uniformly add `msplit` to other monads via monad transformers,
  where computations in a base monad `m` are lifted to computations in a transformed monad `t m`.

  class MonadTrans t where
    lift :: Monad m => m a -> t m a

  Following the laws:
   lift . return  = return
   lift (m >>= k) = lift m >>= lift . k

  The class `LogicT` should have a method `lift` that injects computations `m a` into backtracking computations of
  type `t m a` where `t`. The law of `msplit` should then be generalised to handle the lifted effects from the underlying
  monad `m`, such that `lift m >> mzero` can perform effects before failing.
-}

class MonadTrans t => LogicT t where
  msplitT :: Monad m => t m a -> t m (Maybe (a, t m a))
  {- The rest of the functions: `interleaveT`, `>>-T`, `ifteT`, and `onceT`, can
     also be relocated here from LogicM. -}

{- 5.1 CPS version

   The CPS version of LogicT introduces a type constructor SFKT for functions that accept success and failure continuations.
-}

newtype SFKT m a =
  SFKT { runSFKT :: forall r.
                    (a -> m r -> m r)  -- Success continuation
                 -> m r                -- Failure continuation
                 -> m r
      } deriving (Functor)

instance Applicative (SFKT m)

instance Monad m => Monad (SFKT m) where
  return :: Monad m => a -> SFKT m a
  return a = SFKT (\sk fk -> sk a fk)
  (>>=) :: Monad m => SFKT m a -> (a -> SFKT m b) -> SFKT m b
  m >>= f = SFKT (\sk fk ->
                    -- Construct a new success continuation `sk'` that applies `f` on value `a` to get `SFKT m b`,
                    -- before being provided with the original success continuation `sk`.
                    let sk' = (\a -> runSFKT (f a) sk)
                    in  runSFKT m sk' fk)

instance Monad m => MonadPlus (SFKT m) where
  mzero :: Monad m => SFKT m a
  mzero = SFKT (\_ fk -> fk)
  mplus :: Monad m => SFKT m a -> SFKT m a -> SFKT m a
  m1 `mplus` m2 = SFKT (\sk fk ->
                    -- Construct a new failure continuation `fk'` that first tries running `m2` before failing with the
                    -- original failure continuation `fk`
                    let fk' = runSFKT m2 sk fk
                    in  runSFKT m1 sk fk')

instance MonadTrans SFKT where
  lift :: Monad m => m a -> SFKT m a
  -- Wrap a monadic computation in SFKT by applying the success continuation `sk` to value `a` and failure continuation `fk`
  lift m = SFKT (\sk fk -> m >>= (\a -> sk a fk))

instance LogicT SFKT where
  {- To split a computation tma :: SFKT m a, we supply it with a custom success `ssk` and a custom failure `pure Nothing` continuation.
     If `tma` immediately invokes the failure continuation, we get:
        `lift (pure Nothing)`
     If `tma` invokes the success continuation `ssk`, we return the first answer `a` and a suspension representing the
     exploration of the rest of the computation choices.
  -}
  msplitT :: Monad m => SFKT m a -> SFKT m (Maybe (a, SFKT m a))
  msplitT tma = lift (runSFKT tma ssk (pure Nothing))
    where ssk a fk = pure (Just (a, lift fk >>= \r -> case r of Nothing -> mzero
                                                                Just (b, tmb) -> pure b `mplus` tmb))

-- | Running for all solutions does not need to make use of `msplitT`.
runAll :: Monad m =>  SFKT m a -> m [a]
runAll prog = runSFKT prog sk fk
  where sk a fk = fk >>= pure . (a :)
        fk      = pure []

-- | Running for n solutions uses `msplitT` to accumulate solutions one by one.
runN :: Monad m => Maybe Int -> SFKT m a -> SFKT m [a]
runN Nothing prog = lift $ runAll prog
runN (Just n) prog
  | n <= 0 = pure []
  | otherwise = do
        r <- msplitT prog
        case r of Nothing -> pure []
                  Just (r, prog') -> runN (Just (n - 1)) prog'

prog_1 :: Monad m => m Double
prog_1 = runSFKT (pure 5) sk fk
  where sk a _ = pure a
        fk     = pure 0

prog_2 :: Monad m => m Int
prog_2 = runSFKT (pure 5 `mplus` pure 0) sk fk
  where sk a _ = pure a
        fk     = pure 0

prog_2' :: Monad m => m [Int]
prog_2' = runAll (pure 5 `mplus` pure 0)