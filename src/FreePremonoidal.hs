{-# LANGUAGE GADTs, KindSignatures, LambdaCase, RankNTypes, ScopedTypeVariables, TupleSections, TypeApplications, TypeFamilies, TypeInType, TypeOperators #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fplugin TypeLevel.Rewrite
                -fplugin-opt=TypeLevel.Rewrite:TypeLevel.Append.RightIdentity
                -fplugin-opt=TypeLevel.Rewrite:TypeLevel.Append.RightAssociative #-}
module FreePremonoidal where

import Prelude hiding (id, (.))

import Control.Category
import Data.Kind (Type)
import Data.Proxy
import TypeLevel.Append

import KnownLength
import Premonoidal
import Tuple


data ToList (a :: Type)
            (as :: [Type])
            where
  Unit :: ToList () '[]
  Atom :: ToList a (a ': '[])
  Pair :: ToList a as
       -> ToList b bs
       -> ToList (a, b) (as ++ bs)

type FromList (as :: [Type])
              (a :: Type)
  = ToList a as

data FromSet (as :: [Type])
             (a :: Type)
             where
  FromSet :: ConsumeN as xs '[]
          -> FromList xs a
          -> FromSet as a

data FromSuperset (as :: [Type])
                  (a :: Type)
                  where
  FromSuperset :: ConsumeN as xs _bs
               -> FromList xs a
               -> FromSuperset as a


data Consume1 (as :: [Type])  -- all elements
              (x :: Type)     -- consumed element
              (bs :: [Type])  -- remaining elements
              where
  CHere  :: Consume1 (x ': as) x as
  CThere :: Consume1 as x bs
         -> Consume1 (y ': as) x (y ': bs)

data ConsumeN (as :: [Type])  -- all elements
              (xs :: [Type])  -- consumed elements
              (bs :: [Type])  -- remaining elements
              where
  CNil  :: ConsumeN as '[] as
  CCons :: Consume1 as x bs
        -> ConsumeN bs xs cs
        -> ConsumeN as (x ': xs) cs

data Observe1 (as :: [Type])  -- all elements
              (x :: Type)     -- observed element
              where
  OHere  :: Observe1 (x ': as) x
  OThere :: Observe1 as x
         -> Observe1 (y ': as) x

data ObserveN (as :: [Type])  -- all elements
              (xs :: [Type])  -- observed elements
              where
  ONil  :: ObserveN as '[]
  OCons :: Observe1 as x
        -> ObserveN as xs
        -> ObserveN as (x ': xs)

data ListAction (k :: Type -> Type -> Type)
                (as :: [Type])
                (bs :: [Type])
                where
  ListAction :: FromList as a
             -> k a b
             -> ToList b bs
             -> ListAction k as bs

data Split (prePost :: [Type])
           (pre     :: [Type])
           (post    :: [Type])
           where
  SHere  :: Split as '[] as
  SThere :: Split prePost pre post
         -> Split (a ': prePost) (a ': pre) post

data Focused (action :: [Type] -> [Type] -> Type)
             (as :: [Type])
             (bs :: [Type])
             where
  Focused :: Split (pre ++ as ++ post) pre (as ++ post)
          -> Split (as ++ post) as post
          -> action as bs
          -> Focused action
                     (pre ++ as ++ post)
                     (pre ++ bs ++ post)

data Consuming (action :: [Type] -> [Type] -> Type)
               (as :: [Type])
               (bs :: [Type])
               where
  Consuming :: ConsumeN as xs rest
            -> action xs ys
            -> Consuming action as (ys ++ rest)

data Observing (action :: [Type] -> [Type] -> Type)
               (as :: [Type])
               (bs :: [Type])
               where
  Observing :: ObserveN as xs
            -> action xs ys
            -> Observing action as (ys ++ as)


data FreeCategory (k :: i -> i -> Type)
                  (a :: i)
                  (b :: i)
                  where
  Id     :: FreeCategory k a a
  (:>>>) :: k a b
         -> FreeCategory k b c
         -> FreeCategory k a c

-- Free premonoidal category
data FreePremonoidal (k :: Type -> Type -> Type)
                     (a :: Type)
                     (b :: Type)
                     where
  FreePremonoidal
    :: ToList a as
    -> FreeCategory (Focused (ListAction k)) as bs
    -> FromList bs b
    -> FreePremonoidal k a b

-- Free symmetric premonoidal category
data FreeSymmetric (k :: Type -> Type -> Type)
                   (a :: Type)
                   (b :: Type)
                   where
  FreeSymmetric
    :: ToList a as
    -> FreeCategory (Consuming (ListAction k)) as bs
    -> FromSet bs b
    -> FreeSymmetric k a b

-- Free semicartesian premonoidal category
data FreeSemicartesian (k :: Type -> Type -> Type)
                       (a :: Type)
                       (b :: Type)
                       where
  FreeSemicartesian
    :: ToList a as
    -> FreeCategory (Consuming (ListAction k)) as bs
    -> FromSuperset bs b
    -> FreeSemicartesian k a b

-- Free cartesian premonoidal category
data FreeCartesian (k :: Type -> Type -> Type)
                   (a :: Type)
                   (b :: Type)
                   where
  FreeCartesian
    :: ToList a as
    -> FreeCategory (Observing (ListAction k)) as bs
    -> FromSuperset bs b
    -> FreeCartesian k a b


instance Category (FreeCategory k) where
  id = Id
  (.) = flip go where
    go :: FreeCategory k a b
       -> FreeCategory k b c
       -> FreeCategory k a c
    go Id           gs = gs
    go (f :>>> fs) gs = f :>>> go fs gs


runToListAndLengh
  :: Premonoidal r
  => ToList a as
  -> ( r a (Tuple as)
     , Length as
     )
runToListAndLengh = go1
  where
    go1
      :: Premonoidal r
      => ToList a as
      -> ( r a (Tuple as)
         , Length as
         )
    go1 = \case
      Unit -> let r = -- ()
                      id
                      -- []
              in (r, LNil)
      Atom -> let r = -- a
                      introR
                      -- (a, [])
              in (r, LCons LNil)
      Pair toListL toListR -> go2 toListL toListR

    go2
      :: Premonoidal r
      => ToList a as
      -> ToList b bs
      -> ( r (a, b)
             (Tuple (as ++ bs))
         , Length (as ++ bs)
         )
    go2 toListL toListR
      = let (rL, lenL) = go1 toListL
            (rR, lenR) = go1 toListR
            r          = -- (a, b)
                         first rL
                         -- (as, b)
                     >>> second rR
                         -- (as, bs)
                     >>> tappend lenL lenR
                         -- as ++ bs
        in (r, lappend lenL lenR)

runToList
  :: Premonoidal r
  => ToList a as
  -> r a (Tuple as)
runToList = fst . runToListAndLengh

runFromList
  :: Premonoidal r
  => FromList as a
  -> r (Tuple as) a
runFromList = fst . go1
  where
    go1
      :: Premonoidal r
      => FromList as a
      -> ( r (Tuple as) a
         , Length as
         )
    go1 = \case
      Unit -> let r = -- []
                      id
                      -- ()
              in (r, LNil)
      Atom -> let r = -- (a, [])
                      elimR
                      -- a
              in (r, LCons LNil)
      Pair fromListL fromListR -> go2 fromListL fromListR

    go2
      :: Premonoidal r
      => FromList as a
      -> FromList bs b
      -> ( r (Tuple (as ++ bs))
             (a, b)
         , Length (as ++ bs)
         )
    go2 fromListL fromListR
      = let (rL, lenL) = go1 fromListL
            (rR, lenR) = go1 fromListR
            r          = -- as ++ bs
                         tsplit lenL lenR
                         -- (as, bs)
                     >>> first rL
                         -- (a, bs)
                     >>> second rR
                         -- (a, b)
        in (r, lappend lenL lenR)

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

runConsume1
  :: Symmetric r
  => Consume1 as x bs
  -> r (Tuple as)
       (x, Tuple bs)
runConsume1 = \case
  CHere -> -- (x, as)
           id
           -- (x, as)
  CThere c1 -> -- (y, as)
               second (runConsume1 c1)
               -- (y, (x, bs))
           >>> assocL
               -- ((y, x), bs)
           >>> first swap
               -- ((x, y), bs)
           >>> assocR
               -- (x, (y, bs))

runConsumeN
  :: Symmetric r
  => ConsumeN as xs bs
  -> r (Tuple as)
       (Tuple xs, Tuple bs)
runConsumeN = \case
  CNil -> -- as
          introL
          -- ([], as)
  CCons c1 cN -> -- as
                 runConsume1 c1
                 -- (x, bs)
             >>> second (runConsumeN cN)
                 -- (x, (xs, cs))
             >>> assocL
                 -- ((x, xs), cs)

runObserve1
  :: Semicartesian r
  => Observe1 as x
  -> r (Tuple as) x
runObserve1 = \case
  OHere -> -- (x, as)
           second forget
           -- (x, ())
       >>> elimR
           -- x
  OThere o1 -> -- (y, as)
               second (runObserve1 o1)
               -- (y, x)
           >>> first forget
               -- ((), x)
           >>> elimL

runObserveN
  :: Cartesian r
  => ObserveN as xs
  -> r (Tuple as) (Tuple xs)
runObserveN = \case
  ONil -> -- as
          forget
          -- []
  OCons o1 oN -> -- as
                 dup
                 -- (as, as)
             >>> first (runObserve1 o1)
                 -- (x, as)
             >>> second (runObserveN oN)
                 -- (x, xs)

runListAction
  :: Premonoidal r
  => (forall x y. k x y -> r x y)
  -> ListAction k as bs
  -> ( r (Tuple as) (Tuple bs)
     , Length bs
     )
runListAction runK (ListAction fromList k toList)
  = let (rBs, lenBs) = runToListAndLengh toList
        r            = -- as
                       runFromList fromList
                       -- a
                   >>> runK k
                       -- b
                   >>> rBs
                       -- bs
    in (r, lenBs)

runSplit
   :: Premonoidal r
   => Split prePost pre post
   -> ( r (Tuple prePost)
          (Tuple pre, Tuple post)
      , Length pre
      )
runSplit = \case
  SHere -> let r = -- post
                   introL
                   -- ([], post)
           in (r, LNil)
  SThere s -> let (rS, lenS) = runSplit s
                  r          = -- (a, pre ++ post)
                               second rS
                               -- (a, (pre, post))
                           >>> assocL
                               -- ((a, pre), post)
              in (r, LCons lenS)

runFocused
  :: Premonoidal r
  => (forall xs ys. action xs ys -> ( r (Tuple xs) (Tuple ys)
                                    , Length ys
                                    ))
  -> Focused action as bs
  -> TArrow r as bs
runFocused runAction (Focused s1 s2 action)
  = TArrow $ go runAction s1 s2 action
  where
    go
      :: forall r action pre as bs post. Premonoidal r
      => (forall xs ys. action xs ys -> ( r (Tuple xs) (Tuple ys)
                                        , Length ys
                                        ))
      -> Split (pre ++ as ++ post) pre (as ++ post)
      -> Split (as ++ post) as post
      -> action as bs
      -> r (Tuple (pre ++ as ++ post))
           (Tuple (pre ++ bs ++ post))
    go runAction s1 s2 action
      = let (r1, lenPre) = runSplit s1
            (r2, _lenAs) = runSplit s2
            (rA, lenBs)  = runAction action
            r            = -- pre ++ as ++ post
                           r1
                           -- (pre, as ++ post)
                       >>> second r2
                           -- (pre, (as, post))
                       >>> second (first rA)
                           -- (pre, (bs, post))
                       >>> second (tappend lenBs (Proxy @post))
                           -- (pre, bs ++ post)
                       >>> tappend lenPre (Proxy @(bs ++ post))
                           -- pre ++ bs ++ post
         in r

runConsuming
  :: Symmetric r
  => (forall xs ys. action xs ys -> ( r (Tuple xs) (Tuple ys)
                                    , Length ys
                                    ))
  -> Consuming action as bs
  -> TArrow r as bs
runConsuming runAction (Consuming cN action)
  = TArrow $ go runAction cN action
  where
    go
      :: forall r action as xs ys rest. Symmetric r
      => (forall xs ys. action xs ys -> ( r (Tuple xs) (Tuple ys)
                                        , Length ys
                                        ))
      -> ConsumeN as xs rest
      -> action xs ys
      -> r (Tuple as)
           (Tuple (ys ++ rest))
    go runAction cN action
      = let (rA, lenYs) = runAction action
            r           = -- as
                          runConsumeN cN
                          -- (xs, rest)
                      >>> first rA
                          -- (ys, rest)
                      >>> tappend lenYs (Proxy @rest)
                          -- ys ++ rest
        in r

runObserving
  :: Cartesian r
  => (forall xs ys. action xs ys -> ( r (Tuple xs) (Tuple ys)
                                    , Length ys
                                    ))
  -> Observing action as bs
  -> TArrow r as bs
runObserving runAction (Observing oN action)
  = TArrow $ go runAction oN action
  where
    go
      :: forall r action as xs ys. Cartesian r
      => (forall xs ys. action xs ys -> ( r (Tuple xs) (Tuple ys)
                                        , Length ys
                                        ))
      -> ObserveN as xs
      -> action xs ys
      -> r (Tuple as)
           (Tuple (ys ++ as))
    go runAction oN action
      = let (rA, lenYs) = runAction action
            r           = -- as
                          dup
                          -- (as, as)
                      >>> first (runObserveN oN)
                          -- (xs, as)
                      >>> first rA
                          -- (ys, as)
                      >>> tappend lenYs (Proxy @as)
                          -- ys ++ as
        in r


runFreeCategory
  :: Category r
  => (forall x y. k x y -> r x y)
  -> FreeCategory k a b -> r a b
runFreeCategory runK = \case
  Id        -> id
  f :>>> fs -> runK f
           >>> runFreeCategory runK fs

runFreePremonoidal
  :: forall r k a b. Premonoidal r
  => (forall x y. k x y -> r x y)
  -> FreePremonoidal k a b -> r a b
runFreePremonoidal runK (FreePremonoidal toList
                                         focusedActions
                                         fromList)
    = -- a
      runToList toList
      -- as
  >>> runTArrow (runFreeCategory runAction focusedActions)
      -- bs
  >>> runFromList fromList
      -- b
  where
    runAction
      :: Focused (ListAction k) xs ys
      -> TArrow r xs ys
    runAction = runFocused (runListAction runK)

runFreeSymmetric
  :: forall r k a b. Symmetric r
  => (forall x y. k x y -> r x y)
  -> FreeSymmetric k a b -> r a b
runFreeSymmetric runK (FreeSymmetric toList
                                     consumingActions
                                     fromSet)
    = -- a
      runToList toList
      -- as
  >>> runTArrow (runFreeCategory runAction consumingActions)
      -- bs
  >>> runFromSet fromSet
      -- b
  where
    runAction
      :: Consuming (ListAction k) xs ys
      -> TArrow r xs ys
    runAction = runConsuming (runListAction runK)

runFreeSemicartesian
  :: forall r k a b. Semicartesian r
  => (forall x y. k x y -> r x y)
  -> FreeSemicartesian k a b -> r a b
runFreeSemicartesian runK (FreeSemicartesian toList
                                             consumingActions
                                             fromSuperset)
    = -- a
      runToList toList
      -- as
  >>> runTArrow (runFreeCategory runAction consumingActions)
      -- bs
  >>> runFromSuperset fromSuperset
      -- b
  where
    runAction
      :: Consuming (ListAction k) xs ys
      -> TArrow r xs ys
    runAction = runConsuming (runListAction runK)

runFreeCartesian
  :: forall r k a b. Cartesian r
  => (forall x y. k x y -> r x y)
  -> FreeCartesian k a b -> r a b
runFreeCartesian runK (FreeCartesian toList
                                     observingActions
                                     fromSuperset)
    = -- a
      runToList toList
      -- as
  >>> runTArrow (runFreeCategory runAction observingActions)
  >>> runFromSuperset fromSuperset
  where
    runAction
      :: Observing (ListAction k) xs ys
      -> TArrow r xs ys
    runAction = runObserving (runListAction runK)
