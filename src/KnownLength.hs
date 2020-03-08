{-# LANGUAGE DataKinds, GADTs, LambdaCase, RankNTypes, TypeOperators #-}
module KnownLength where

import TypeLevel.Append


data Length as where
  LNil  :: Length '[]
  LCons :: Length as
        -> Length (a ': as)

lappend
  :: Length as
  -> Length bs
  -> Length (as ++ bs)
lappend LNil         lenB = lenB
lappend (LCons lenA) lenB = LCons (lappend lenA lenB)


class KnownLength as where
  knownLength :: Length as

instance KnownLength '[] where
  knownLength = LNil

instance KnownLength as => KnownLength (a ': as) where
  knownLength = LCons knownLength

withKnownLength
  :: Length as
  -> (KnownLength as => r)
  -> r
withKnownLength = \case
  LNil -> \r -> r
  LCons len -> withKnownLength len
