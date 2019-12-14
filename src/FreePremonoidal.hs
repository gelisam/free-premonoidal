{-# LANGUAGE GADTs, KindSignatures, TypeFamilies, TypeInType, TypeOperators #-}
module Main where
import Test.DocTest

import Data.Kind (Type)
import Data.Proxy


type family (++) (as :: [Type])
                 (bs :: [Type])
                 where
  '[]       ++ bs = bs
  (a ': as) ++ bs = a ': (as ++ bs)


data ToList (a :: Type)
            (as :: [Type])
            where
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
  FromSet :: GrabN xs '[] as
          -> FromList xs a
          -> FromSet as a

data FromSuperset (as :: [Type])
                  (a :: Type)
                  where
  FromSuperset :: GrabN xs xs' as
               -> FromList xs a
               -> FromSuperset as a


data Grab1 (x :: Type)
           (as :: [Type])
           (bs :: [Type])
           where
  Grab1 :: ( as ~ (left ++ right)
           , bs ~ (left ++ '[x] ++ right)
           )
        => Proxy left -> Proxy x -> Proxy right
        -> Grab1 x as bs

data GrabN (xs :: [Type])
           (as :: [Type])
           (bs :: [Type])
            where
  NilG  :: GrabN '[] '[] bs
  ConsG :: Grab1 x as bs
        -> GrabN xs bs cs
        -> GrabN (x ': xs) as cs


data Reuse1 (x :: Type)
            (as :: [Type])
            where
  Reuse1 :: ( as ~ (left ++ '[x] ++ right)
            )
         => Proxy left -> Proxy x -> Proxy right
         -> Reuse1 x as

data ReuseN (xs :: [Type])
            (as :: [Type])
            where
  NilR  :: ReuseN '[] as
  ConsR :: Reuse1 x as
        -> ReuseN xs as
        -> ReuseN (x ': xs) as


data ListAction (k :: Type -> Type -> Type)
                (as :: [Type])
                (bs :: [Type])
                where
  ListAction :: FromList as a
             -> k a b
             -> ToList b bs
             -> ListAction k as bs

data PortionAction (action :: [Type] -> [Type] -> Type)
                   (as :: [Type])
                   (bs :: [Type])
                   where
  PortionAction :: ( as ~ (left ++ as' ++ right)
                   , bs ~ (left ++ bs' ++ right)
                   )
                => Proxy left
                -> action as' bs'
                -> Proxy right
                -> PortionAction k as bs

data GrabAction (action :: [Type] -> [Type] -> Type)
                (as :: [Type])
                (bs :: [Type])
                where
  GrabAction :: GrabN as' rest as
             -> action as' bs'
             -> GrabAction action as (bs' ++ rest)

data ReuseAction (action :: [Type] -> [Type] -> Type)
                 (as :: [Type])
                 (bs :: [Type])
                 where
  ReuseAction :: ReuseN as' as
              -> action as' bs'
              -> ReuseAction action as (bs' ++ as)


data FreeCategory (k :: Type -> Type -> Type)
                  (a :: Type)
                  (b :: Type)
                  where
  NilC  :: FreeCategory k a a
  ConsC :: k a b
        -> FreeCategory k b c
        -> FreeCategory k a c

data Actions (action :: [Type] -> [Type] -> Type)
             (as :: [Type])
             (bs :: [Type])
             where
  NilA  :: Actions action as as
  ConsA :: action as bs
        -> Actions action bs cs
        -> Actions action as cs

-- Free premonoidal category
data FreePremonoidal (k :: Type -> Type -> Type)
                     (a :: Type)
                     (b :: Type)
                     where
  FreePremonoidal
    :: ToList a as
    -> Actions (PortionAction (ListAction k)) as bs
    -> FromList bs b
    -> FreePremonoidal k a b


-- Free symmetric premonoidal category
data FreeSymmetric (k :: Type -> Type -> Type)
          (a :: Type)
          (b :: Type)
          where
  FreeSymmetric
    :: ToList a as
    -> Actions (GrabAction (ListAction k)) as bs
    -> FromSet bs b
    -> FreeSymmetric k a b

-- Free semicartesian premonoidal category
data FreeSemicartesian (k :: Type -> Type -> Type)
                       (a :: Type)
                       (b :: Type)
                       where
  FreeSemicartesian
    :: ToList a as
    -> Actions (GrabAction (ListAction k)) as bs
    -> FromSuperset bs b
    -> FreeSemicartesian k a b

-- Free cartesian premonoidal category
data FreeCartesian (k :: Type -> Type -> Type)
                   (a :: Type)
                   (b :: Type)
                   where
  FreeCartesian
    :: ToList a as
    -> Actions (ReuseAction (ListAction k)) as bs
    -> FromSuperset bs b
    -> FreeCartesian k a b


main :: IO ()
main = doctest ["src/Main.hs"]
