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


data Action (k :: Type -> Type -> Type)
            (as :: [Type])
            (bs :: [Type])
            where
  Action :: FromList as a
         -> k a b
         -> ToList b bs
         -> Action k as bs

data Actions (action :: [Type] -> [Type] -> Type)
             (as :: [Type])
             (bs :: [Type])
             where
  NilA  :: Actions action as as
  ConsA :: GrabN as' rest as
        -> action as' bs'
        -> Actions action (bs' ++ rest) cs
        -> Actions action as cs

-- Free semicartesian premonoidal category
data Free (k :: Type -> Type -> Type)
          (a :: Type)
          (b :: Type)
          where
  Free
    :: ToList a as
    -> Actions (Action k) as bs
    -> FromSuperset bs b
    -> Free k a b



main :: IO ()
main = doctest ["src/Main.hs"]
