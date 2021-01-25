{-# LANGUAGE DataKinds, GADTs, KindSignatures, TypeFamilies, TypeOperators #-}
module Data.Graph.Dag where

import Data.Proxy
import GHC.TypeLits


type family ZipAdd (as :: [Nat]) (bs :: [Nat]) = (rs :: [Nat]) where
  ZipAdd '[]       bs        = bs
  ZipAdd as        '[]       = as
  ZipAdd (a ': as) (b ': bs) = (a + b) ': ZipAdd as bs

-- 'as' is the number of incoming edges of the next node, the node after it,
-- etc.
data Dag (as :: [Nat]) where
  Nil
    :: Dag '[]

  -- x edges incoming, y0 edges from this node to the next, y1 nodes from this
  -- node to the node after that, etc.
  Cons
    :: Proxy ys
    -> Dag (ZipAdd as ys)
    -> Dag (x ': as)
