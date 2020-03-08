{-# LANGUAGE GADTs, KindSignatures, LambdaCase, RankNTypes, ScopedTypeVariables, TupleSections, TypeApplications, TypeFamilies, TypeInType, TypeOperators #-}
{-# OPTIONS_GHC -fplugin TypeLevel.Rewrite
                -fplugin-opt=TypeLevel.Rewrite:TypeLevel.Append.RightIdentity
                -fplugin-opt=TypeLevel.Rewrite:TypeLevel.Append.RightAssociative #-}
module FreePremonoidal where

import Prelude hiding (id, (.))

import Control.Category
import Data.Kind (Type)
import Data.Proxy
import TypeLevel.Append


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
  CHere  :: Consume1 (x ': as) x as
  CThere :: Consume1 as x bs
         -> Consume1 (y ': as) x (y ': bs)

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
  OHere  :: Observe1 (x ': as) x
  OThere :: Observe1 as x
         -> Observe1 (y ': as) x

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

data Split (prePost :: [Type])
           (pre     :: [Type])
           (post    :: [Type])
           where
  SHere  :: Split as '[] as
  SThere :: Split prePost pre post
         -> Split (a ': prePost) (a ': pre) post

data Focused (action :: [Type] -> [Type] -> Type)
             (as :: [Type])
             (bs :: [Type])
             where
  Focused :: Split (pre ++ as ++ post) pre (as ++ post)
          -> Split (as ++ post) as post
          -> action as bs
          -> Focused action
                     (pre ++ as ++ post)
                     (pre ++ bs ++ post)

data Consuming (action :: [Type] -> [Type] -> Type)
               (as :: [Type])
               (bs :: [Type])
               where
  Consuming :: ConsumeN as xs rest
            -> action xs ys
            -> Consuming action as (ys ++ rest)

data Observing (action :: [Type] -> [Type] -> Type)
               (as :: [Type])
               (bs :: [Type])
               where
  Observing :: ObserveN as xs
            -> action xs ys
            -> Observing action as (ys ++ as)


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


data HList as where
  HNil  :: HList '[]
  HCons :: a -> HList as -> HList (a ': as)

happend :: HList as -> HList bs -> HList (as ++ bs)
happend HNil         ys = ys
happend (HCons x xs) ys = HCons x (happend xs ys)


newtype HArrow as bs = HArrow
  { runHArrow :: HList as -> HList bs }

instance Category HArrow where
  id = HArrow id
  HArrow f . HArrow g = HArrow (f . g)


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
  -> HList bs -> b
runFromList fromList = fst . go1 (Proxy @'[]) fromList
  where
    go1
      :: Proxy rest
      -> FromList bs b
      -> HList (bs ++ rest) -> (b, HList rest)
    go1 Proxy = \case
      Unit -> \rest -> ((), rest)
      Atom -> \(HCons b rest)
           -> (b, rest)
      Pair l r -> go2 l r

    go2 :: forall as bs a b rest
         . FromList as a
        -> FromList bs b
        -> HList ((as ++ bs) ++ rest)
        -> ((a, b), HList rest)
    go2 l r asBsRest
      = let (a, bsRest) = go1 (Proxy @(bs ++ rest))
                              l asBsRest
            (b, rest)   = go1 (Proxy @_)
                              r bsRest
        in ((a, b), rest)

runFromSet
  :: FromSet as a
  -> HList as -> a
runFromSet (FromSet cN fromList) as
  = let (xs, _) = runConsumeN cN as
        a       = runFromList fromList xs
    in a

runFromSuperset
  :: FromSuperset as a
  -> HList as -> a
runFromSuperset (FromSuperset cN fromList) as
  = let (xs, _) = runConsumeN cN as
        a       = runFromList fromList xs
    in a

runConsume1
  :: Consume1 as x bs
  -> HList as -> (x, HList bs)
runConsume1 = \case
  CHere -> \(HCons x as) -> (x, as)
  CThere c1 -> \(HCons y as)
            -> let (x, bs) = runConsume1 c1 as
               in (x, HCons y bs)

runConsumeN
  :: ConsumeN as xs bs
  -> HList as -> (HList xs, HList bs)
runConsumeN = \case
  CNil -> \as -> (HNil, as)
  CCons c1 cN -> \as
              -> let (x, bs)  = runConsume1 c1 as
                     (xs, cs) = runConsumeN cN bs
                 in (HCons x xs, cs)

runObserve1
  :: Observe1 as x
  -> HList as -> x
runObserve1 = \case
  OHere -> \(HCons x _) -> x
  OThere o1 -> \(HCons _ as) -> runObserve1 o1 as

runObserveN
  :: ObserveN as xs
  -> HArrow as xs
runObserveN = \case
  ONil -> HArrow $ \_ -> HNil
  OCons o1 oN -> HArrow $ \as
              -> HCons (runObserve1 o1 as)
                       (runHArrow (runObserveN oN) as)

runListAction
  :: (forall x y. k x y -> x -> y)
  -> ListAction k as bs
  -> HArrow as bs
runListAction runK (ListAction fromList k toList)
    = HArrow
    $ runFromList fromList
  >>> runK k
  >>> runToList toList

runSplit
   :: Split prePost pre post
   -> HList prePost -> (HList pre, HList post)
runSplit = \case
  SHere -> \as -> (HNil, as)
  SThere s -> \(HCons a prePost)
           -> let (pre, post) = runSplit s prePost
              in (HCons a pre, post)

runFocused
  :: (forall xs ys. action xs ys -> HArrow xs ys)
  -> Focused action as bs
  -> HArrow as bs
runFocused runAction (Focused s1 s2 action) = HArrow $ \preAsPost
 -> let (pre, asPost) = runSplit s1 preAsPost
        (as, post)    = runSplit s2 asPost
        bs            = runHArrow (runAction action) as
    in pre `happend` bs `happend` post

runConsuming
  :: (forall xs ys. action xs ys -> HArrow xs ys)
  -> Consuming action as bs
  -> HArrow as bs
runConsuming runAction (Consuming cN action) = HArrow $ \as
  -> let (xs, rest) = runConsumeN cN as
         ys         = runHArrow (runAction action) xs
     in ys `happend` rest

runObserving
  :: (forall xs ys. action xs ys -> HArrow xs ys)
  -> Observing action as bs
  -> HArrow as bs
runObserving runAction (Observing cN action) = HArrow $ \as
  -> let xs = runHArrow (runObserveN cN) as
         ys = runHArrow (runAction action) xs
     in ys `happend` as


runFreeCategory
  :: Category r
  => (forall x y. k x y -> r x y)
  -> FreeCategory k a b -> r a b
runFreeCategory runK = \case
  Id        -> id
  f :>>> fs -> runK f
           >>> runFreeCategory runK fs

runFreePremonoidal
  :: (forall x y. k x y -> x -> y)
  -> FreePremonoidal k a b
  -> a -> b
runFreePremonoidal runK (FreePremonoidal toList focusedActions fromList)
    = runToList toList
  >>> runHArrow (runFreeCategory (runFocused $ runListAction $ runK)
                                 focusedActions)
  >>> runFromList fromList

runFreeSymmetric
  :: (forall x y. k x y -> x -> y)
  -> FreeSymmetric k a b
  -> a -> b
runFreeSymmetric runK (FreeSymmetric toList consumingActions fromSet)
    = runToList toList
  >>> runHArrow (runFreeCategory (runConsuming $ runListAction $ runK)
                                 consumingActions)
  >>> runFromSet fromSet

runFreeSemicartesian
  :: (forall x y. k x y -> x -> y)
  -> FreeSemicartesian k a b
  -> a -> b
runFreeSemicartesian runK (FreeSemicartesian toList observingActions fromSuperset)
    = runToList toList
  >>> runHArrow (runFreeCategory (runConsuming $ runListAction $ runK)
                                 observingActions)
  >>> runFromSuperset fromSuperset

runFreeCartesian
  :: (forall x y. k x y -> x -> y)
  -> FreeCartesian k a b
  -> a -> b
runFreeCartesian runK (FreeCartesian toList observingActions fromSuperset)
    = runToList toList
  >>> runHArrow (runFreeCategory (runObserving $ runListAction $ runK)
                                 observingActions)
  >>> runFromSuperset fromSuperset
