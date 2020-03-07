{-# LANGUAGE GADTs, KindSignatures, LambdaCase, RankNTypes, TupleSections, TypeFamilies, TypeInType, TypeOperators #-}
{-# OPTIONS_GHC -fplugin TypeLevel.Rewrite
                -fplugin-opt=TypeLevel.Rewrite:TypeLevel.Append.RightIdentity
                -fplugin-opt=TypeLevel.Rewrite:TypeLevel.Append.RightAssociative #-}
module FreePremonoidal where

import Prelude hiding (id, (.))

import qualified Control.Arrow as K
import Control.Category
import Data.Kind (Type)
import Data.Proxy
import TypeLevel.Append


-- premonoidal category
class Category k => Premonoidal k where
  first  :: k a b
         -> k (a, x) (b, x)
  second :: k a b
         -> k (x, a) (x, b)
  introL :: k a ((), a)
  introR :: k a (a, ())
  elimL  :: k ((), a) a
  elimR  :: k (a, ()) a
  assocL :: k (a, (b, c))
              ((a, b), c)
  assocR :: k ((a, b), c)
              (a, (b, c))

-- symmetric premonoidal category
class Premonoidal k => Symmetric k where
  swap :: k (a, b) (b, a)

-- semicartesian premonoidal category
class Symmetric k => Semicartesian k where
  forget :: k a ()

-- cartesian premonoidal category
class Semicartesian k => Cartesian k where
  dup :: k a (a, a)


instance Premonoidal (->) where
  first  = K.first
  second = K.second
  introL a = ((), a)
  introR a = (a, ())
  elimL  ((), a) = a
  elimR  (a, ()) = a
  assocL (a, (b, c)) = ((a, b), c)
  assocR ((a, b), c) = (a, (b, c))

instance Symmetric (->) where
  swap (a, b) = (b, a)

instance Semicartesian (->) where
  forget a = ()

instance Cartesian (->) where
  dup a = (a, a)


instance Monad m => Premonoidal (K.Kleisli m) where
  first  = K.first
  second = K.second
  introL = K.arr introL
  introR = K.arr introR
  elimL  = K.arr elimL
  elimR  = K.arr elimR
  assocL = K.arr assocL
  assocR = K.arr assocR

instance Monad m => Symmetric (K.Kleisli m) where
  swap = K.arr swap

instance Monad m => Semicartesian (K.Kleisli m) where
  forget = K.arr forget

instance Monad m => Cartesian (K.Kleisli m) where
  dup = K.arr dup


data ToList (a :: Type)
            (as :: [Type])
            where
  Unit :: ToList () '[]
  Atom :: ToList a (a ': '[])
  Pair :: ToList a as
       -> ToList b bs
       -> ToList (a, b) (as ++ bs)

type FromList (bs :: [Type])
              (b :: Type)
  = ToList b bs

data FromSet (as :: [Type])
             (a :: Type)
             where
  FromSet :: ConsumeN as xs '[]
          -> FromList xs a
          -> FromSet as a

data FromSuperset (as :: [Type])
                  (a :: Type)
                  where
  FromSuperset :: ConsumeN as xs _bs
               -> FromList xs a
               -> FromSuperset as a


data Consume1 (as :: [Type])  -- all elements
              (x :: Type)     -- consumed element
              (bs :: [Type])  -- remaining elements
              where
  Consume1 :: ( as ~ (left ++ '[x] ++ right)
              , bs ~ (left ++ right)
              )
           => Proxy left -> Proxy x -> Proxy right
           -> Consume1 as x bs

data ConsumeN (as :: [Type])  -- all elements
              (xs :: [Type])  -- consumed elements
              (bs :: [Type])  -- remaining elements
              where
  CNil  :: ConsumeN as '[] as
  CCons :: Consume1 as x bs
        -> ConsumeN bs xs cs
        -> ConsumeN as (x ': xs) cs


data Observe1 (as :: [Type])  -- all elements
              (x :: Type)     -- observed element
              where
  Observe1 :: ( as ~ (left ++ '[x] ++ right)
              )
           => Proxy left -> Proxy x -> Proxy right
           -> Observe1 as x

data ObserveN (as :: [Type])  -- all elements
              (xs :: [Type])  -- observed elements
              where
  ONil  :: ObserveN as '[]
  OCons :: Observe1 as x
        -> ObserveN as xs
        -> ObserveN as (x ': xs)


data ListAction (k :: Type -> Type -> Type)
                (as :: [Type])
                (bs :: [Type])
                where
  ListAction :: FromList as a
             -> k a b
             -> ToList b bs
             -> ListAction k as bs

data Focused (action :: [Type] -> [Type] -> Type)
             (as :: [Type])
             (bs :: [Type])
             where
  Focused :: ( as ~ (left ++ as' ++ right)
             , bs ~ (left ++ bs' ++ right)
             )
          => Proxy left
          -> action as' bs'
          -> Proxy right
          -> Focused k as bs

data Consuming (action :: [Type] -> [Type] -> Type)
               (as :: [Type])
               (bs :: [Type])
               where
  Consuming :: ConsumeN as as' rest
            -> action as' bs'
            -> Consuming action as (bs' ++ rest)

data Observing (action :: [Type] -> [Type] -> Type)
               (as :: [Type])
               (bs :: [Type])
               where
  Observing :: ObserveN as as'
            -> action as' bs'
            -> Observing action as (bs' ++ as)


data FreeCategory (k :: i -> i -> Type)
                  (a :: i)
                  (b :: i)
                  where
  Id     :: FreeCategory k a a
  (:>>>) :: k a b
         -> FreeCategory k b c
         -> FreeCategory k a c


-- Free premonoidal category
data FreePremonoidal (k :: Type -> Type -> Type)
                     (a :: Type)
                     (b :: Type)
                     where
  FreePremonoidal
    :: ToList a as
    -> FreeCategory (Focused (ListAction k)) as bs
    -> FromList bs b
    -> FreePremonoidal k a b


-- Free symmetric premonoidal category
data FreeSymmetric (k :: Type -> Type -> Type)
                   (a :: Type)
                   (b :: Type)
                   where
  FreeSymmetric
    :: ToList a as
    -> FreeCategory (Consuming (ListAction k)) as bs
    -> FromSet bs b
    -> FreeSymmetric k a b

-- Free semicartesian premonoidal category
data FreeSemicartesian (k :: Type -> Type -> Type)
                       (a :: Type)
                       (b :: Type)
                       where
  FreeSemicartesian
    :: ToList a as
    -> FreeCategory (Consuming (ListAction k)) as bs
    -> FromSuperset bs b
    -> FreeSemicartesian k a b

-- Free cartesian premonoidal category
data FreeCartesian (k :: Type -> Type -> Type)
                   (a :: Type)
                   (b :: Type)
                   where
  FreeCartesian
    :: ToList a as
    -> FreeCategory (Observing (ListAction k)) as bs
    -> FromSuperset bs b
    -> FreeCartesian k a b


instance Category (FreeCategory k) where
  id = Id
  (.) = flip go where
    go :: FreeCategory k a b
       -> FreeCategory k b c
       -> FreeCategory k a c
    go Id           gs = gs
    go (f :>>> fs) gs = f :>>> go fs gs

runFreeCategory
  :: Category r
  => (forall x y. k x y -> r x y)
  -> FreeCategory k a b -> r a b
runFreeCategory runK = \case
  Id        -> id
  f :>>> fs -> runK f
           >>> runFreeCategory runK fs


data HList as where
  HNil  :: HList '[]
  HCons :: a -> HList as -> HList (a ': as)

happend :: HList as -> HList bs -> HList (as ++ bs)
happend HNil         ys = ys
happend (HCons x xs) ys = HCons x (happend xs ys)


runToList
  :: ToList a as
  -> a -> HList as
runToList = \case
  Unit -> \() -> HNil
  Atom -> \a -> HCons a HNil
  Pair l r -> \(a, b)
           -> happend (runToList l a)
                      (runToList r b)

runFromList
  :: FromList bs b
  -> HList (bs ++ rest) -> (b, HList rest)
runFromList = \case
  Unit -> \rest -> ((), rest)
  Atom -> \(HCons b rest) -> (b, rest)
  Pair l r -> go l r
  where
    go :: forall as bs a b rest
        . FromList as a
       -> FromList bs b
       -> HList ((as ++ bs) ++ rest)
       -> ((a, b), HList rest)
    go l r asBsRest = let (a, bsRest) = runFromList l asBsRest
                          (b, rest)   = runFromList r bsRest
                      in ((a, b), rest)
