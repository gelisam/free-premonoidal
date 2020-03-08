{-# LANGUAGE DataKinds, LambdaCase, TypeFamilies, TypeOperators #-}
module Tuple where

import Prelude hiding (id, (.))

import Control.Category

import KnownLength
import Premonoidal
import TypeLevel.Append


type family Tuple as where
  Tuple '[]       = ()
  Tuple (a ': as) = (a, Tuple as)

tappend
  :: Premonoidal r
  => Length as
  -> Length bs
  -> r (Tuple as, Tuple bs)
       (Tuple (as ++ bs))
tappend = \case
  LNil -> \_ -> -- ([], bs)
                elimL
                -- bs
  LCons lenA -> \lenB
             -> -- (a, as), bs)
                assocR
                -- (a, (as, bs))
            >>> second (tappend lenA lenB)
                -- (a, as ++ bs)

tsplit
  :: Premonoidal r
  => Length as
  -> Length bs
  -> r (Tuple (as ++ bs))
       (Tuple as, Tuple bs)
tsplit = \case
  LNil -> \_ -> -- bs
                introL
                -- ([], bs)
  LCons lenA -> \lenB
             -> -- (a, as ++ bs)
                second (tsplit lenA lenB)
                -- (a, (as, bs))
            >>> assocL
                -- ((a, as), bs)
