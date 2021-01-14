{-# LANGUAGE DataKinds, KindSignatures, PolyKinds, TypeOperators #-}
module Premonoidal where

import Prelude hiding (id, (.))

import Control.Category
import Data.Kind (Type)
import Data.Proxy

import TypeLevel.Append


-- premonoidal category
--
-- e.g. [a, b, cd]
--       | q1 :: q [a, b] ab
--      [ab, cd]
--           | q2 :: q cd [c, d]
--      [ab, c, d]
--       | q3 :: q ab []
--      [c, d]
--           | q4 :: q [] e
--      [c, d, e]
--
-- true in a monoidal category but not in a premonoidal category:
--   (f *** id) >>> (id *** g) = f *** g = (id *** g) >>> (f *** id)
--   first f >>> second g  =  second g >>> first f
class Category q
   => Premonoidal (q :: [k] -> [k] -> Type) where
  first
    :: q as bs
    -> Proxy zs
    -> q (as ++ zs) (bs ++ zs)
  second
    :: Proxy xs
    -> q as bs
    -> q (xs ++ as) (xs ++ bs)


--instance Premonoidal (->) where
--  first  = K.first
--  second = K.second
--
--instance Monad m => Premonoidal (K.Kleisli m) where
--  first  = K.first
--  second = K.second
