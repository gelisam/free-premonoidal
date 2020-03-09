{-# LANGUAGE DataKinds, LambdaCase, TypeFamilies, TypeOperators #-}
module Tuple where

import Prelude hiding (id, (.))

import Control.Category

import KnownLength
import Premonoidal
import TypeLevel.Append


-- Tuple [x1, x2, x3] = (x1, (x2, (x3, ())))
type family Tuple as where
  Tuple '[]       = ()
  Tuple (a ': as) = (a, Tuple as)

tappend
  :: Premonoidal r
  => Length as
  -> proxy bs
  -> r (Tuple as, Tuple bs)
       (Tuple (as ++ bs))
tappend = \case
  LNil -> \_
       -> -- ([], bs)
          elimL
          -- bs
  LCons lenA -> \proxyB
             -> -- (a, as), bs)
                assocR
                -- (a, (as, bs))
            >>> second (tappend lenA proxyB)
                -- (a, as ++ bs)

tsplit
  :: Premonoidal r
  => Length as
  -> proxy bs
  -> r (Tuple (as ++ bs))
       (Tuple as, Tuple bs)
tsplit = \case
  LNil -> \_
       -> -- bs
          introL
          -- ([], bs)
  LCons lenA -> \proxyB
             -> -- (a, as ++ bs)
                second (tsplit lenA proxyB)
                -- (a, (as, bs))
            >>> assocL
                -- ((a, as), bs)


newtype TArrow r as bs = TArrow
  { runTArrow :: r (Tuple as) (Tuple bs) }

instance Category r => Category (TArrow r) where
  id = TArrow id
  TArrow f . TArrow g = TArrow (f . g)
