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
   -> r (Tuple prePost)
        (Tuple pre, Tuple post)
runDivide = \case
  DHere -> -- post
           introL
           -- ([], post)
  DThere d -> -- (a, pre ++ post)
              second (runDivide d)
              -- (a, (pre, post))
          >>> assocL
              -- ((a, pre), post)

runDividing
  :: Premonoidal r
  => (forall xs ys. action xs ys -> r (Tuple xs) (Tuple ys))
  -> (forall xs ys. action xs ys -> Length ys)
  -> Dividing action as bs
  -> TArrow r as bs
runDividing runAction outputLength (Dividing d1 d2 action)
  = TArrow $ go runAction outputLength d1 d2 action
  where
    go
      :: forall r action pre as bs post. Premonoidal r
      => (forall xs ys. action xs ys -> r (Tuple xs) (Tuple ys))
      -> (forall xs ys. action xs ys -> Length ys)
      -> Divide (pre ++ as ++ post) pre (as ++ post)
      -> Divide (as ++ post) as post
      -> action as bs
      -> r (Tuple (pre ++ as ++ post))
           (Tuple (pre ++ bs ++ post))
    go runAction outputLength d1 d2 action
        = -- pre ++ as ++ post
          runDivide d1
          -- (pre, as ++ post)
      >>> second (runDivide d2)
          -- (pre, (as, post))
      >>> second (first (runAction action))
          -- (pre, (bs, post))
      >>> second (tappend (outputLength action)
                          (Proxy @post))
          -- (pre, bs ++ post)
      >>> tappend (prefixLength d1)
                  (Proxy @(bs ++ post))
          -- pre ++ bs ++ post

prefixLength
  :: Divide (pre ++ post) pre post
  -> Length pre
prefixLength = \case
  DHere -> LNil
  DThere d -> LCons (prefixLength d)

divide
  :: Length pre
  -> proxy post
  -> Divide (pre ++ post) pre post
divide = \case
  LNil -> \_ -> DHere
  LCons len -> \_ -> DThere (divide len Proxy)

singletonDividing
  :: forall action pre as proxy bs post
   . Length pre
  -> Length as
  -> proxy post
  -> action as bs
  -> Dividing action (pre ++ as ++ post)
                     (pre ++ bs ++ post)
singletonDividing lenPre lenAs proxyPost action
  = Dividing (divide lenPre (Proxy @(as ++ post)))
             (divide lenAs proxyPost)
             action
