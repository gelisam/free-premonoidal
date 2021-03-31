{-# LANGUAGE AllowAmbiguousTypes, DataKinds, GADTs, PolyKinds, RankNTypes, ScopedTypeVariables, TypeFamilies, TypeOperators #-}
module TypeLevel.List where

import Data.Kind (Type)
import Data.Constraint (Dict, withDict)
import Data.Proxy
import TypeLevel.Append

import TypeLevel.Axiom


nilP
  :: Proxy '[]
nilP
  = Proxy

appendP
  :: Proxy xs
  -> Proxy ys
  -> Proxy (xs ++ ys)
appendP Proxy Proxy
  = Proxy

withAssoc
  :: forall xs ys zs r
   . ( ((xs ++ ys) ++ zs)
     ~ (xs ++ (ys ++ zs))
    => r
     )
  -> r
withAssoc r
  = withDict (axiom :: Dict ( ((xs ++ ys) ++ zs)
                            ~ (xs ++ (ys ++ zs))
                            ))
             r


data Singleton
       (q :: k -> k -> Type)
       (as :: [k])
       (bs :: [k])
       where
  Singleton
    :: q a b
    -> Singleton q '[a] '[b]

data UnSingleton
       (q :: [k] -> [k] -> Type)
       (a :: k)
       (b :: k)
       where
  UnSingleton
    :: q '[a] '[b]
    -> UnSingleton q a b

data TensorTree
       (t :: k -> k -> k)
       (a :: k)
       (as :: [k])
       where
  Fork
    :: TensorTree t a as
    -> TensorTree t b bs
    -> TensorTree t (a `t` b) (as ++ bs)
  Leaf
    :: TensorTree t a '[a]

data Tensored
       (t :: k -> k -> k)
       (q :: k -> k -> Type)
       (as :: [k])
       (bs :: [k])
       where
  Tensored
    :: TensorTree t a as
    -> q a b
    -> TensorTree t b bs
    -> Tensored t q as bs

data UnTensored
       (t :: k -> k -> k)
       (q :: [k] -> [k] -> Type)
       (a :: k)
       (b :: k)
       where
  UnTensored
    :: TensorTree t a as
    -> q as bs
    -> TensorTree t b bs
    -> UnTensored t q a b
