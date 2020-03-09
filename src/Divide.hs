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


-- e.g. Divide [a, b, c, x, y] [a, b, c] [x, y]
data Divide (prePost :: [Type])
            (pre     :: [Type])
            (post    :: [Type])
            where
  DHere  :: Divide as '[] as
  DThere :: Divide prePost pre post
         -> Divide (a ': prePost) (a ': pre) post

-- e.g.
-- action :: r [x1, x2] [y1, y2, y3]
-- Dividing _ _ action :: Dividing r [a, b, x1, x2, c, d, e]
--                                   [a, b, y1, y2, y3, c, d, e]
data Dividing (action :: [Type] -> [Type] -> Type)
              (as :: [Type])
              (bs :: [Type])
              where
  Dividing :: Divide (pre ++ as ++ post) pre (as ++ post)
           -> Divide (as ++ post) as post
           -> action as bs
           -> Dividing action
                       (pre ++ as ++ post)
                       (pre ++ bs ++ post)

runDivide
   :: Premonoidal r
   => Divide prePost pre post
   -> ( r (Tuple prePost)
          (Tuple pre, Tuple post)
      , Length pre
      )
runDivide = \case
  DHere -> let r = -- post
                   introL
                   -- ([], post)
           in (r, LNil)
  DThere d -> let (rD, lenD) = runDivide d
                  r          = -- (a, pre ++ post)
                               second rD
                               -- (a, (pre, post))
                           >>> assocL
                               -- ((a, pre), post)
              in (r, LCons lenD)

runDividing
  :: Premonoidal r
  => (forall xs ys. action xs ys -> ( r (Tuple xs) (Tuple ys)
                                    , Length ys
                                    ))
  -> Dividing action as bs
  -> TArrow r as bs
runDividing runAction (Dividing d1 d2 action)
  = TArrow $ go runAction d1 d2 action
  where
    go
      :: forall r action pre as bs post. Premonoidal r
      => (forall xs ys. action xs ys -> ( r (Tuple xs) (Tuple ys)
                                        , Length ys
                                        ))
      -> Divide (pre ++ as ++ post) pre (as ++ post)
      -> Divide (as ++ post) as post
      -> action as bs
      -> r (Tuple (pre ++ as ++ post))
           (Tuple (pre ++ bs ++ post))
    go runAction d1 d2 action
      = let (r1, lenPre) = runDivide d1
            (r2, _lenAs) = runDivide d2
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
