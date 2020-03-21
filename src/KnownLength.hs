{-# LANGUAGE DataKinds, GADTs, LambdaCase, RankNTypes, TypeOperators #-}
module KnownLength where

import Data.Proxy
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

one
  :: Length '[a]
one
  = LCons LNil

lcompare
  :: (as ++ as') ~ (bs ++ bs')
  => Length as
  -> proxy as'
  -> Length bs
  -> proxy bs'
  -> ( forall p post
     . (as ++ (p ': post)) ~ bs
    => Proxy p
    -> Proxy post
    -> r
     )  -- ^ Length as <= Length bs
  -> ( as ~ bs
    => r
     )  -- ^ Length as == Length bs
  -> ( forall p post
     . as ~ (bs ++ (p ': post))
    => Proxy p
    -> Proxy post
    -> r
     )
  -> r
lcompare LNil _
         LNil _
         _ ccEq _ = ccEq
lcompare LNil _
         (LCons _) _
         ccLt _ _ = ccLt Proxy Proxy
lcompare (LCons _) _
         LNil _
         _ _ ccGt = ccGt Proxy Proxy
lcompare (LCons lenAs) proxyAs'
         (LCons lenBs) proxyBs'
         ccLt ccEq ccGt = lcompare lenAs proxyAs'
                                   lenBs proxyBs'
                                   ccLt ccEq ccGt


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
