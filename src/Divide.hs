{-# LANGUAGE DataKinds, GADTs, KindSignatures, LambdaCase, RankNTypes, ScopedTypeVariables, TypeApplications, TypeOperators #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fplugin TypeLevel.Rewrite
                -fplugin-opt=TypeLevel.Rewrite:TypeLevel.Append.RightIdentity
                -fplugin-opt=TypeLevel.Rewrite:TypeLevel.Append.RightAssociative #-}
module Divide where

import Prelude hiding (id, (.))

import Control.Category
import Data.Kind (Type)
import Data.Proxy
import TypeLevel.Append

import KnownLength
import Premonoidal
import Tuple


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
