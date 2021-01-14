{-# LANGUAGE DataKinds, KindSignatures, PolyKinds, TypeFamilies, TypeOperators #-}
module TypeLevel.List where

import Data.Proxy
import TypeLevel.Append


nilP :: Proxy '[]
nilP = Proxy

appendP :: Proxy xs -> Proxy ys -> Proxy (xs ++ ys)
appendP Proxy Proxy = Proxy
