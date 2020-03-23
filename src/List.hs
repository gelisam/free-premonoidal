{-# LANGUAGE DataKinds, EmptyCase, GADTs, KindSignatures, LambdaCase, RankNTypes, ScopedTypeVariables, TypeApplications, TypeOperators #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fplugin TypeLevel.Rewrite
                -fplugin-opt=TypeLevel.Rewrite:TypeLevel.Append.RightIdentity
                -fplugin-opt=TypeLevel.Rewrite:TypeLevel.Append.RightAssociative #-}
module List where

import Prelude hiding (id, (.))

import Control.Category
import Data.Kind (Type)
import Data.Proxy
import TypeLevel.Append

import Consume
import KnownLength
import Premonoidal
import Tuple


-- e.g.
-- ToList ((a, ()), ((), b)) [(a, ()), ((), b)]
-- ToList ((a, ()), ((), b)) [a, (), (), b]
-- ToList ((a, ()), ((), b)) [a, b]
data ToList (a :: Type)
            (as :: [Type])
            where
  Unit :: ToList () '[]
  Atom :: ToList a (a ': '[])
  Pair :: ToList a as
       -> ToList b bs
       -> ToList (a, b) (as ++ bs)

-- e.g. FromList [a, b, c, d] ((a, b), (c, d))
type FromList (as :: [Type])
              (a :: Type)
  = ToList a as

-- e.g. FromSet [b, c, a, d] ((a, b), (c, d))
data FromSet (as :: [Type])
             (a :: Type)
             where
  FromSet :: ConsumeN as xs '[]
          -> FromList xs a
          -> FromSet as a

-- e.g. FromSet [x, b, c, y, a, d, z] ((a, b), (c, d))
data FromSuperset (as :: [Type])
                  (a :: Type)
                  where
  FromSuperset :: ConsumeN as xs _bs
               -> FromList xs a
               -> FromSuperset as a

-- e.g.
-- f :: k (x1, x2) (y1, (y2, y3))
-- ListAction _ _ action :: ListAction k [x1, x2]
--                                       [y1, y2 y3]
data ListAction (k :: Type -> Type -> Type)
                (as :: [Type])
                (bs :: [Type])
                where
  ListAction :: FromList as a
             -> k a b
             -> ToList b bs
             -> ListAction k as bs

listLength
  :: ToList a as
  -> Length as
listLength = \case
  Unit -> LNil
  Atom -> one
  Pair l r -> listLength l
    `lappend` listLength r

runToList
  :: Premonoidal r
  => ToList a as
  -> r a (Tuple as)
runToList = go1
  where
    go1
      :: Premonoidal r
      => ToList a as
      -> r a (Tuple as)
    go1 = \case
      Unit -> -- ()
              id
              -- []
      Atom -> -- a
              introR
              -- (a, [])
      Pair toListL toListR -> go2 toListL toListR

    go2
      :: Premonoidal r
      => ToList a as
      -> ToList b bs
      -> r (a, b)
           (Tuple (as ++ bs))
    go2 toListL toListR
        = -- (a, b)
          first (go1 toListL)
          -- (as, b)
      >>> second (go1 toListR)
          -- (as, bs)
      >>> tappend (listLength toListL)
                  (listLength toListR)
          -- as ++ bs

runFromList
  :: Premonoidal r
  => FromList as a
  -> r (Tuple as) a
runFromList = go1
  where
    go1
      :: Premonoidal r
      => FromList as a
      -> r (Tuple as) a
    go1 = \case
      Unit -> -- []
              id
              -- ()
      Atom -> -- (a, [])
              elimR
              -- a
      Pair fromListL fromListR -> go2 fromListL fromListR

    go2
      :: Premonoidal r
      => FromList as a
      -> FromList bs b
      -> r (Tuple (as ++ bs))
           (a, b)
    go2 fromListL fromListR
        = -- as ++ bs
          tsplit (listLength fromListL)
                 (listLength fromListR)
          -- (as, bs)
      >>> first (go1 fromListL)
          -- (a, bs)
      >>> second (go1 fromListR)
          -- (a, b)
runFromSet
  :: Symmetric r
  => FromSet as a
  -> r (Tuple as) a
runFromSet (FromSet cN fromList)
    = -- as
      runConsumeN cN
      -- (xs, [])
  >>> elimR
      -- xs
  >>> runFromList fromList
      -- a

runFromSuperset
  :: Semicartesian r
  => FromSuperset as a
  -> r (Tuple as) a
runFromSuperset (FromSuperset cN fromList)
    = -- as
      runConsumeN cN
      -- (xs, bs)
  >>> second forget
      -- (xs, ()
  >>> elimR
      -- xs
  >>> runFromList fromList
      -- a

runListAction
  :: Premonoidal r
  => (forall x y. k x y -> r x y)
  -> ListAction k as bs
  -> r (Tuple as) (Tuple bs)
runListAction runK (ListAction fromList k toList)
    = -- as
      runFromList fromList
      -- a
  >>> runK k
      -- b
  >>> runToList toList
      -- bs

listActionOutputLength
  :: ListAction k as bs
  -> Length bs
listActionOutputLength (ListAction _ _ toList)
  = listLength toList

singletonToList
  :: ToList a '[a]
singletonToList
  = Atom

singletonFromList
  :: FromList '[a] a
singletonFromList
  = Atom

singletonFromSet
  :: FromSet '[a] a
singletonFromSet
  = FromSet singletonConsumeN
            singletonFromList

singletonFromSuperset
  :: FromSuperset '[a] a
singletonFromSuperset
  = FromSuperset singletonConsumeN
                 singletonFromList

removeUnitAt
  :: Length pre
  -> proxy post
  -> ToList a (pre ++ ('[()] ++ post))
  -> ToList a (pre ++ post)
removeUnitAt LNil _ Atom = Unit
removeUnitAt (LCons lenPre) _ Atom = case lenPre of {}
removeUnitAt lenPre proxyPost (Pair l r)
  = go lenPre proxyPost l r
  where
    go
      :: forall proxy pre post l ls r rs
       . (pre ++ (() ': post)) ~ (ls ++ rs)
      => Length pre
      -> proxy post
      -> ToList l ls
      -> ToList r rs
      -> ToList (l, r) (pre ++ post)
    go lenPre proxyPost l r
      = lcompare lenPre (Proxy @(() ': post))
                 (listLength l) (Proxy @rs)
                 ccLt ccEq ccGt
      where
        ccLt
          :: ls ~ (pre ++ (() ': xs))
          => Proxy ()
          -> Length xs
          -> ToList (l, r) (pre ++ xs ++ rs)
        ccLt Proxy lenXs
          = Pair (removeUnitAt lenPre lenXs l)
                 r

        ccEq
          :: rs ~ (() ': post)
          => ToList (l, r) (ls ++ post)
        ccEq
          = Pair l
                 (removeUnitAt LNil proxyPost r)

        ccGt
          :: rs ~ ((x ': xs) ++ (() ': post))
          => Proxy x
          -> Length xs
          -> ToList (l, r) (ls ++ (x ': xs) ++ post)
        ccGt Proxy lenXs
          = Pair l
                 (removeUnitAt (LCons lenXs) proxyPost r)

splitPairAt
  :: Length pre
  -> proxy1 a1
  -> proxy2 a2
  -> proxy3 post
  -> ToList a (pre ++ ('[(a1, a2)] ++ post))
  -> ToList a (pre ++ ('[a1, a2] ++ post))
splitPairAt LNil _ _ _ Atom = Pair Atom Atom
splitPairAt (LCons lenPre) _ _ _ Atom = case lenPre of {}
splitPairAt lenPre proxyA1 proxyA2 proxyPost (Pair l r)
  = go lenPre proxyA1 proxyA2 proxyPost l r
  where
    go
      :: forall proxy1 proxy2 proxy3 pre a1 a2 post l ls r rs
       . (pre ++ ((a1, a2) ': post)) ~ (ls ++ rs)
      => Length pre
      -> proxy1 a1
      -> proxy2 a2
      -> proxy3 post
      -> ToList l ls
      -> ToList r rs
      -> ToList (l, r) (pre ++ '[a1, a2] ++ post)
    go lenPre proxyA1 proxyA2 proxyPost l r
      = lcompare lenPre (Proxy @((a1, a2) ': post))
                 (listLength l) (Proxy @rs)
                 ccLt ccEq ccGt
      where
        ccLt
          :: ls ~ (pre ++ ((a1, a2) ': xs))
          => Proxy (a1, a2)
          -> Length xs
          -> ToList (l, r) (pre ++ '[a1, a2] ++ xs ++ rs)
        ccLt Proxy lenXs
          = Pair (splitPairAt lenPre proxyA1 proxyA2 lenXs l)
                 r

        ccEq
          :: rs ~ ((a1, a2) ': post)
          => ToList (l, r) (ls ++ '[a1, a2] ++ post)
        ccEq = Pair l (splitPairAt LNil proxyA1 proxyA2 proxyPost r)

        ccGt
          :: rs ~ ((x ': xs) ++ ('[(a1, a2)] ++ post))
          => Proxy x
          -> Length xs
          -> ToList (l, r) (ls ++ (x ': xs) ++ '[a1, a2] ++ post)
        ccGt Proxy lenXs
          = Pair l
                 (splitPairAt (LCons lenXs) proxyA1 proxyA2 proxyPost r)

-- Even with TypeLevel.Rewrite, it is sometimes necessary to manually apply
-- rewrite rules. I think it's because when ghc knows that xs ~ (as ++ bs), it
-- automatically simplifies ((as ++ bs) ++ cs) to (xs ++ cs), thereby preventing
-- the typechecker plugin from rewriting ((as ++ bs) ++ cs) to (as ++ (bs ++ cs)).
withAssoc
  :: Proxy as
  -> Proxy bs
  -> Proxy cs
  -> ( ((as ++ bs) ++ cs)
     ~ (as ++ (bs ++ cs))
    => r
     )
  -> r
withAssoc Proxy Proxy Proxy r = r

compareLists
  :: forall a as1 as2 result
   . ToList a as1
  -> ToList a as2
  -> ( as1 ~ as2
    => result
     )  -- ^ toList1 == toList2
  -> ( forall pre post
     . as1 ~ (pre ++ '[()] ++ post)
    => Length pre
    -> Proxy post
    -> result
     )  -- ^ a Unit in toList1 could by removed
  -> ( forall pre post
     . as2 ~ (pre ++ '[()] ++ post)
    => Length pre
    -> Proxy post
    -> result
     )  -- ^ a Unit in toList2 could by removed
  -> ( forall pre l r post
     . as1 ~ (pre ++ '[(l,r)] ++ post)
    => Length pre
    -> Proxy l
    -> Proxy r
    -> Proxy post
    -> result
     )  -- ^ an Atom in toList1 could by split
  -> ( forall pre l r post
     . as2 ~ (pre ++ '[(l,r)] ++ post)
    => Length pre
    -> Proxy l
    -> Proxy r
    -> Proxy post
    -> result
     )  -- ^ an Atom in toList2 could by split
  -> result
compareLists toList1 toList2 ccEq ccUnit1 ccUnit2 ccPair1 ccPair2
  = go2 toList1 toList2
  where
    go2
      :: ToList a as1
      -> ToList a as2
      -> result
    go2 Unit Unit = ccEq
    go2 Atom Atom = ccEq
    go2 (Pair l1 r1)
        (Pair l2 r2)
      = go4 l1 r1 l2 r2

    go2 Atom Unit = ccUnit1 LNil Proxy
    go2 Unit Atom = ccUnit2 LNil Proxy

    go2 Atom (Pair _ _) = ccPair1 LNil Proxy Proxy Proxy
    go2 (Pair _ _) Atom = ccPair2 LNil Proxy Proxy Proxy

    go4
      :: forall l ls1 ls2
                r rs1 rs2
       . ( a ~ (l,r)
         , as1 ~ (ls1 ++ rs1)
         , as2 ~ (ls2 ++ rs2)
         )
      => ToList l ls1
      -> ToList r rs1
      -> ToList l ls2
      -> ToList r rs2
      -> result
    go4 lToLs1 rToRs1 lToLs2 rToRs2
      = compareLists lToLs1 lToLs2
                     ccEqL ccUnitL1 ccUnitL2 ccPairL1 ccPairL2
      where
        ccEqL
          :: ls1 ~ ls2
          => result
        ccEqL
          = compareLists rToRs1 rToRs2
                         ccEqR ccUnitR1 ccUnitR2 ccPairR1 ccPairR2

        ccUnitL1
          :: forall pre post
           . ls1 ~ (pre ++ '[()] ++ post)
          => Length pre
          -> Proxy post
          -> result
        ccUnitL1 lenPre Proxy
          = -- as1 ~ ((pre ++ '[()]) ++ post) ++ rs1
            withAssoc (Proxy @(pre ++ '[()]))
                      (Proxy @post)
                      (Proxy @rs1)
          $ -- as1 ~ (pre ++ '[()]) ++ (post ++ rs1)
            ccUnit1 lenPre
                    (Proxy @(post ++ rs1))

        ccUnitL2
          :: forall pre post
           . ls2 ~ (pre ++ '[()] ++ post)
          => Length pre
          -> Proxy post
          -> result
        ccUnitL2 lenPre Proxy
          = -- as2 ~ ((pre ++ '[()]) ++ post) ++ rs2
            withAssoc (Proxy @(pre ++ '[()]))
                      (Proxy @post)
                      (Proxy @rs2)
          $ -- as2 ~ (pre ++ '[()]) ++ (post ++ rs2)
            ccUnit2 lenPre
                    (Proxy @(post ++ rs2))

        ccPairL1
          :: forall pre l1 r1 post
           . ls1 ~ (pre ++ '[(l1,r1)] ++ post)
          => Length pre
          -> Proxy l1
          -> Proxy r1
          -> Proxy post
          -> result
        ccPairL1 lenPre Proxy Proxy Proxy
          = -- as1 ~ ((pre ++ '[(l1,r1)]) ++ post) ++ rs1
            withAssoc (Proxy @(pre ++ '[(l1,r1)]))
                      (Proxy @post)
                      (Proxy @rs1)
          $ -- as1 ~ (pre ++ '[(l1,r1)]) ++ (post ++ rs1)
            ccPair1 lenPre
                    (Proxy @l1)
                    (Proxy @r1)
                    (Proxy @(post ++ rs1))

        ccPairL2
          :: forall pre l2 r2 post
           . ls2 ~ (pre ++ '[(l2,r2)] ++ post)
          => Length pre
          -> Proxy l2
          -> Proxy r2
          -> Proxy post
          -> result
        ccPairL2 lenPre Proxy Proxy Proxy
          = -- as2 ~ ((pre ++ '[(l2,r2)]) ++ post) ++ rs2
            withAssoc (Proxy @(pre ++ '[(l2,r2)]))
                      (Proxy @post)
                      (Proxy @rs2)
          $ -- as2 ~ (pre ++ '[(l2,r2)]) ++ (post ++ rs2)
            ccPair2 lenPre
                    (Proxy @l2)
                    (Proxy @r2)
                    (Proxy @(post ++ rs2))

        ccEqR
          :: ( ls1 ~ ls2
             , rs1 ~ rs2
             )
          => result
        ccEqR
          = ccEq

        ccUnitR1
          :: forall pre post
           . rs1 ~ (pre ++ '[()] ++ post)
          => Length pre
          -> Proxy post
          -> result
        ccUnitR1 lenPre proxyPost
          = -- as1 ~ ls1 ++ ((pre ++ '[()]) ++ post)
            withAssoc (Proxy @pre)
                      (Proxy @'[()])
                      (Proxy @post)
          $ -- as1 ~ ls1 ++ (pre ++ ('[()] ++ post))
            withAssoc (Proxy @ls1)
                      (Proxy @pre)
                      (Proxy @('[()] ++ post))
          $ -- as1 ~ (ls1 ++ pre) ++ ('[()] ++ post)
            ccUnit1 (listLength lToLs1 `lappend` lenPre)
                    proxyPost

        ccUnitR2
          :: forall pre post
           . rs2 ~ (pre ++ '[()] ++ post)
          => Length pre
          -> Proxy post
          -> result
        ccUnitR2 lenPre proxyPost
          = -- as2 ~ ls2 ++ ((pre ++ '[()]) ++ post)
            withAssoc (Proxy @pre)
                      (Proxy @'[()])
                      (Proxy @post)
          $ -- as2 ~ ls2 ++ (pre ++ ('[()] ++ post))
            withAssoc (Proxy @ls2)
                      (Proxy @pre)
                      (Proxy @('[()] ++ post))
          $ -- as2 ~ (ls2 ++ pre) ++ ('[()] ++ post)
            ccUnit2 (listLength lToLs2 `lappend` lenPre)
                    proxyPost

        ccPairR1
          :: forall pre l1 r1 post
           . rs1 ~ (pre ++ '[(l1,r1)] ++ post)
          => Length pre
          -> Proxy l1
          -> Proxy r1
          -> Proxy post
          -> result
        ccPairR1 lenPre proxyL1 proxyL2 proxyPost
          = -- as1 ~ ls1 ++ ((pre ++ '[(l1,r1)]) ++ post)
            withAssoc (Proxy @ls1)
                      (Proxy @(pre ++ '[(l1,r1)]))
                      (Proxy @post)
          $ -- as1 ~ (ls1 ++ (pre ++ '[(l1,r1)])) ++ post
            withAssoc (Proxy @ls1)
                      (Proxy @pre)
                      (Proxy @'[(l1,r1)])
          $ -- as1 ~ ((ls1 ++ pre) ++ '[(l1,r1)]) ++ post
            ccPair1 (listLength lToLs1 `lappend` lenPre)
                    proxyL1 proxyL2 proxyPost

        ccPairR2
          :: forall pre l2 r2 post
           . rs2 ~ (pre ++ '[(l2,r2)] ++ post)
          => Length pre
          -> Proxy l2
          -> Proxy r2
          -> Proxy post
          -> result
        ccPairR2 lenPre proxyL1 proxyL2 proxyPost
          = -- as2 ~ ls2 ++ ((pre ++ '[(l2,r2)]) ++ post)
            withAssoc (Proxy @ls2)
                      (Proxy @(pre ++ '[(l2,r2)]))
                      (Proxy @post)
          $ -- as2 ~ (ls2 ++ (pre ++ '[(l2,r2)])) ++ post
            withAssoc (Proxy @ls2)
                      (Proxy @pre)
                      (Proxy @'[(l2,r2)])
          $ -- as2 ~ ((ls2 ++ pre) ++ '[(l2,r2)]) ++ post
            ccPair2 (listLength lToLs2 `lappend` lenPre)
                    proxyL1 proxyL2 proxyPost

composeLists
  :: forall a as x bs b result
   . ToList a as
  -> FromList as x
  -> ToList x bs
  -> FromList bs b
  -> ( forall xs
     . ToList a xs
    -> FromList xs b
    -> result
     )
  -> result
composeLists aToAs asToX xToBs bsToB cc
  = compareLists asToX xToBs
                 ccEq ccUnitA ccUnitB ccPairA ccPairB
  where
    ccEq
      :: as ~ bs
      => result
    ccEq
      = cc aToAs bsToB

    ccUnitA
      :: forall pre post
       . as ~ (pre ++ '[()] ++ post)
      => Length pre
      -> Proxy post
      -> result
    ccUnitA lenPre proxyPost
      = -- as ~ (pre ++ '[()]) ++ post
        withAssoc (Proxy @pre)
                  (Proxy @'[()])
                  (Proxy @post)
      $ -- as ~ pre ++ ('[()] ++ post)
        composeLists (removeUnitAt lenPre proxyPost aToAs)
                     (removeUnitAt lenPre proxyPost asToX)
                     xToBs bsToB
                     cc

    ccUnitB
      :: forall pre post
       . bs ~ (pre ++ '[()] ++ post)
      => Length pre
      -> Proxy post
      -> result
    ccUnitB lenPre proxyPost
      = -- bs ~ (pre ++ '[()]) ++ post
        withAssoc (Proxy @pre)
                  (Proxy @'[()])
                  (Proxy @post)
      $ -- bs ~ pre ++ ('[()] ++ post)
        composeLists aToAs asToX
                     (removeUnitAt lenPre proxyPost xToBs)
                     (removeUnitAt lenPre proxyPost bsToB)
                     cc

    ccPairA
      :: forall pre l r post
       . as ~ (pre ++ '[(l,r)] ++ post)
      => Length pre
      -> Proxy l
      -> Proxy r
      -> Proxy post
      -> result
    ccPairA lenPre proxyL proxyR proxyPost
      = -- as ~ ((pre ++ '[(l,r)]) ++ post)
        withAssoc (Proxy @pre)
                  (Proxy @'[(l,r)])
                  (Proxy @post)
      $ -- as ~ (pre ++ '[(l,r)]) ++ post
        composeLists (splitPairAt lenPre proxyL proxyR proxyPost aToAs)
                     (splitPairAt lenPre proxyL proxyR proxyPost asToX)
                     xToBs bsToB
                     cc

    ccPairB
      :: forall pre l r post
       . bs ~ (pre ++ '[(l,r)] ++ post)
      => Length pre
      -> Proxy l
      -> Proxy r
      -> Proxy post
      -> result
    ccPairB lenPre proxyL proxyR proxyPost
      = -- bs ~ ((pre ++ '[(l,r)]) ++ post)
        withAssoc (Proxy @pre)
                  (Proxy @'[(l,r)])
                  (Proxy @post)
      $ -- bs ~ (pre ++ '[(l,r)]) ++ post
        composeLists aToAs asToX
                     (splitPairAt lenPre proxyL proxyR proxyPost xToBs)
                     (splitPairAt lenPre proxyL proxyR proxyPost bsToB)
                     cc
