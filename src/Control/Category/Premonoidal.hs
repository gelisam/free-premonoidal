{-# LANGUAGE DataKinds, KindSignatures, PolyKinds, TypeOperators #-}
module Control.Category.Premonoidal where

import Prelude hiding (id, (.))

import Control.Category
import Data.Kind (Type)
import Data.Proxy

import TypeLevel.Append


-- A Premonoidal category can be seen as a Category with more structure, or as
-- Linear types with more restrictions.
--
-- In a Category, the output of each morphism is the input of the next
-- morphism; that is, this input is completely consumed by the next morphism.
-- With Premonoidal, a morphism is allowed to only consume a fraction of its
-- input. The way this works is that there are two morphisms: the thin
-- morphism, which only consumes a fraction of its input, and the wide
-- morphism, which consumes the entire input, but does so in a way which leaves
-- untouched the parts of the input which are not consumed by the thin
-- morphism.
--
-- In Premonoidal, the portion which is consumed must be a sub-list of
-- consecutive elements of the input. Linear lifts that restrictions to allow
-- any subset of the input. Premonoidal's restrictiveness is sometimes useful.
-- For example, in https://github.com/gelisam/category-syntax#wire-diagrams,
-- the values represent wires and we want to force the user to choose which
-- wire passes over the other whenever the wires cross.
--
-- For example, the wire diagram
--
--     a  b     c  d
--     |  |     |  |
--      \ |     |  |
--        \     |  |
--        | \   |  |
--       /   | /   |
--      |    /     |
--      |  / |     | _
--      | |  |     /   \
--      | |  |   / |    |
--      | |  |  |  |    |
--      | |  |  |  |    |
--      b c  a  e  d    f
--
-- Can be represented as
--
-- >     -- [a, b, c, d]
-- >     widen (Proxy @[])
-- >           (over :: q [a, b] [b, a])
-- >           (Proxy @[c, d])
-- >     -- [b, a, c, d]
-- > >>> widen (Proxy @[b])
-- >           (under :: q [a, c] [c, a])
-- >           (Proxy @[d])
-- >     -- [b, c, a, d]
-- > >>> widen (Proxy @[b, c, a, d])
-- >           (cap :: q [] [e, f])
-- >           (Proxy @[])
-- >     -- [b, c, a, d, e, f]
-- > >>> widen (Proxy @[b, c, a])
-- >           (under :: q [d, e] [e, d])
-- >           (Proxy @[f])
-- >     -- [b, c, a, e, d, f]
--
-- Each morphism may perform arbitrary side-effects. This is different from a
-- monoidal category, in which side-effects are forbidden because of the
-- following law, which requires effects to commute:
--
-- >   (f *** id) >>> (id *** g) = f *** g = (id *** g) >>> (f *** id)
-- >   first f >>> second g  =  second g >>> first f
--
-- The above law does _not_ need to hold for Premonoidal instances.
class Category q
   => Premonoidal (q :: [k] -> [k] -> Type) where
  widen
    :: Proxy xs
    -> q as bs
    -> Proxy zs
    -> q (xs ++ as ++ zs) (xs ++ bs ++ zs)
