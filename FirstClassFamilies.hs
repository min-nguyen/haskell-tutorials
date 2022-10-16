{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances, PolyKinds, DataKinds, TypeFamilies, TypeOperators, UndecidableInstances, FunctionalDependencies, ScopedTypeVariables, TypeApplications #-}
import Prelude hiding (map)
import Data.Kind
import GHC.Natural
import GHC.TypeLits (Nat)
import qualified GHC.TypeLits as TL

{- Data kinds allows us to promote types to kinds and constructors to types.
   For example, promoting the data type for booleans, gives us apostrophe True and apostrophe False as types, and Bool as a kind. -}

-- data Bool = True | False
-- kind Bool = 'True | 'False

{- Where data kinds become super useful is when doing type-level programming, which is essentially computation on types. We can think of *type families* as functions at the type-level. Consider the regular term-level function "or" which computes the "or" of two booleans.
-}

or :: Bool -> Bool -> Bool
or True _  = True
or False y = y

{-**Type families allow us to perform type-level programming**-}
{- We can't automatically promote term-level functions into type-level ones. However, if we enable -XTypeFamilies, then we can promote a function by explicitly duplicating its logic as a closed type family.
-}
{- This says that Or is a type family, which takes two types x and y of kind Bool, and then outputs a type of kind Bool. So this can be seen as the 'or' function promoted to the type-level. Instead of values and types, we work with types and kinds. -}
type family Or (x :: Bool) (y :: Bool) :: Bool where
  Or 'True y = 'True
  Or 'False y = y

{-There's a big problem with type families however - they must be fully saturated. We cannot partially apply type families like we can with functions - all of its parameters must be specified at the same time.
As an example, consider the map function which applies a function f over all the elements of a list: -}

map :: (a -> b) -> [a] -> [b]
map _ []       = []
map f (a : as) = f a : map f as

{-We can create a type-level equivalent of this using type-families. -}

type family Map (f :: a -> b) (xs :: [a]) :: [b] where
  Map f '[]       = '[]
  Map f (x ': xs) = f x ': Map f xs

{- But this isn't really if we can't partially apply type-families. As an example, let's create a type family for adding two nats together.-}

type family Add (x :: Nat) (y :: Nat) :: Nat where
  Add x y = x TL.+ y

{- Let's now try mapping the function 'Add 1' over a list of nats.
type L = Map (Add 1) '[1, 2, 3]
This will complain that (Add) is supposed to be applied to two arguments.
-}

{- A way to deal with this is called "Defunctionalization", this is a way of reprsenting functional values as pure data values instead. -}

{-**Defunctionalization: Representing functions as data values which can be evaluated **-}

{- I'll show what this looks like at the term level first. -}

{-**Defunctionalization at the Term-level**-}

{- Given the function 'fst' -}
fst :: (a, b) -> a
fst (x, y) = x

{- There are two steps: -}
{- 1) First, we represent a function a data type whose constructor holds all of the arguments of the function.
We'll call these data type equivalent versions of functions "defunctionalized labels". -}

-- | Defunctionalized label
data Fst a b = Fst (a, b)

{- 2) Second, we can then implement an evaluation function for "defunctionalized labels", codified as a typeclass with a functional dependency.
This says that given a defunctionalized label "dfl", this completely determines the return type "r", and we can in fact evaluate l to r. -}

-- | Evaluating a defunctionalized label 'dfl' to result type 'r'
class Eval' dfl r | dfl -> r where
  eval' :: dfl -> r

{- We can now write an instance of evaluation for the label 'Fst' -}

instance Eval' (Fst a b) a where
  eval' (Fst (a, b)) = a

{- So this seems like a very roundabout approach of doing things, but it works just as well as the function-version of fst - we could consider these two approaches isomorphic. -}

{- The cool thing about this is that the idea of defunctionalization can be lifted to the type-level. -}

{-**Defunctionalization at the Type-level**-}

{- First we need to introduce a kind synonym - Exp a describes a type-level function which when evaluated, will produce a type of kind 'a'.  -}

type Exp a = a -> Type

{- Then we write a type family 'Eval', which corresponds to the type-level equivalent of the type class 'Eval'.
It performs evaluation on a type of kind 'Exp a' and to return a type of kind 'a' -}

type family Eval (e :: Exp a) :: a

{- To demonstrate how defunctionalization works with types, let's create a defunctionalized type-level version of the function snd. -}
snd :: (a, b) -> b
snd (x, y) = y

{- First, we need to write a defunctionalized label for this function.
When we're doing defunctionalization at the type-level, we represent functions as empty data types whose kind signature mirrors the type signature of our function. -}
data Snd :: (a, b) -> Exp b
{- This says that:
The kind of Snd is (a, b) -> b -> Type
-}

{- We can now evaluate the defunctionalized label Snd by implementing an instance of the Eval type family-}
type instance Eval (Snd '(a, b)) = b
{- I can show this works in ghci by writing:
> :set -XDataKinds
> kind! Eval (Snd '("stranger", "danger"))
-}

{- Okay so this is all cool, but we haven't really got a solution for partially applying type-level higher-order functions yet.
So lets try and lift the function 'map' to the type-level. -}

mapList :: (a -> b) -> [a] -> [b]
mapList f []      = []
mapList f (x:xs)  = f x : mapList f xs

{- Like before, first we represent this as a defunctionalized label by writing it as an empty data type, where its kind signature mirrors the type signature of our function.
-}

data MapList :: (a -> Exp b) -> [a] -> Exp [b]

{- Note that every argument which is also a function must also be defunctionalized.
This is why we have an Exp wrapping the output of the mapped function as well as wrapping the final output of MapList. -}

{- We can now evaluate the defunctionalized label MapList, by implementing instances of the Eval type family. Notice that we don't just prepend (f x) to the front of the list, but we also evaluate it - this makes sure that we can propagate the evaluation of further defunctionalized labels in the type. -}

type instance Eval (MapList f '[]) = '[]
type instance Eval (MapList f (x ': xs)) = Eval (f x) ': Eval (MapList f xs)

{-
And i can show that this works:
> :kind! Eval (MapList Snd '[ '("help", "me"), '("i'm", "suffering")])
-}

{- So this gives us the power to do proper type-level programming.  -}


------------------------------------------------------------------------------------------------

{- So let's take a real problem and try to solve it at the type level.

There's a function called findIndex, which when given a boolean condition, searches through a list and returns the element of the first element which satisfies that condition.
-}

findIndex :: (a -> Bool) -> [a] -> Maybe Int
findIndex cond [] = Nothing
findIndex cond (x:xs) =
  if cond x then Just 0 else findIndex cond xs >>= return . (+1)

{- We want to turn promote this into a function which finds a type in a type level list.
There are a number of term-level operations which we'll need to find a way of representing at the type-level. -}

{- Notice that we're always working in the Exp type - we evaluate types of Exp.
   Interestingly enough, Exp a is a type-level monad.
   We can create defunctionalized labels for pure and bind. -}
data Pure :: a -> Exp a
data (>>=) :: Exp a -> (a -> Exp b) -> Exp b
infixl 0 >>=
type instance Eval (Pure a) = a
type instance Eval (mx >>= mf) = Eval (mf (Eval mx))
{- Another functionality we'll need is to fmap over Maybe types -}
data FMap :: (a -> Exp b) -> f a -> Exp (f b)
type instance Eval (FMap f 'Nothing)  = 'Nothing
type instance Eval (FMap f ('Just a)) = 'Just (Eval (f a))
{- We'll create a defunctionalized version of addition as well -}
data (+) :: Nat -> Nat -> Exp Nat
type instance Eval ((+) a b) = a TL.+ b
{- We also need a type level version of if-statements -}
data If :: Bool -> a -> a -> Exp a
type instance Eval (If 'True a1 a2) = a1
type instance Eval (If 'False a1 a2) = a2
{- We can finally implement FindIndex. First we make a defunctionalized label for it, so the data type's kind signature mirrors the type signature we want. -}
data FindIndex :: (a -> Exp Bool) -> [a] -> Exp (Maybe Nat)
{- Of course, applying findindex to an empty list should return nothing-}
type instance Eval (FindIndex f '[]) = 'Nothing
{- When we apply find index to a non-empty list -}
type instance Eval (FindIndex f (x ': xs))
{- the first thing we check is whether a condition holds -}
  = Eval (If (Eval (f x))
{- If it does then we return Just 0-}
             (Eval (Pure ('Just 0)))
{- Otherwise, we continue finding the index, and then add 1 onto the result. -}
             (Eval (FindIndex f xs >>= FMap ((+) 1))))

{- As a condition, we create a type-level version of equality.
   We make a type family for equality between types. -}
type family TyEqImpl (a :: k) (b :: k) :: Bool where
  TyEqImpl a a = 'True
  TyEqImpl a b = 'False
-- Then we make a defunctionalised label for type equality
data TyEq :: a -> b -> Exp Bool
-- Evaluating TyEq a b is equivalent to the TyEqImpl a b
type instance Eval (TyEq a b) = TyEqImpl a b

{- And finally, i can show you that this works:
> :kind! Eval (FindIndex (TyEq Bool) '[Int, Double, Bool])
This can be used for implementing things such as open sums and open records.
-}

