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
  :: forall as as' bs bs' proxy1 proxy2 r. (as ++ as') ~ (bs ++ bs')
  => Length as
  -> proxy1 as'
  -> Length bs
  -> proxy2 bs'
  -> ( forall x xs
     . ( (as ++ (x ': xs)) ~ bs
       , as' ~ ((x ': xs) ++ bs')
       )
    => Proxy x
    -> Length xs
    -> r
     )  -- ^ Length as <= Length bs
  -> ( ( as ~ bs
       , as' ~ bs'
       )
    => r
     )  -- ^ Length as == Length bs
  -> ( forall x xs
     . ( as ~ (bs ++ (x ': xs))
       , bs' ~ ((x ': xs) ++ as')
       )
    => Proxy x
    -> Length xs
    -> r
     )  -- ^ Length as >= Length bs
  -> r
lcompare LNil _
         LNil _
         _ ccEq _ = ccEq
lcompare LNil _
         (LCons len) _
         ccLt _ _ = ccLt Proxy len
lcompare (LCons len) _
         LNil _
         _ _ ccGt = ccGt Proxy len
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
