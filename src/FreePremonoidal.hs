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
  Nil  :: Actions action as as
  Cons :: ( as ~ (left ++ as' ++ right)
          , bs ~ (left ++ bs' ++ right)
          )
       => Proxy left -> action as' bs' -> Proxy right
       -> Actions action bs cs
       -> Actions action as cs

-- Free premonoidal category
data Free (k :: Type -> Type -> Type)
          (a :: Type)
          (b :: Type)
          where
  Free
    :: ToList a as
    -> Actions (Action k) as bs
    -> FromList bs b
    -> Free k a b



main :: IO ()
main = doctest ["src/Main.hs"]
