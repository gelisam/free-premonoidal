{-# LANGUAGE DataKinds, GADTs, LambdaCase, RankNTypes, TypeOperators #-}
module KnownLength where


data Length as where
  LNil  :: Length '[]
  LCons :: Length as
        -> Length (a ': as)

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
  LCons l -> withKnownLength l
