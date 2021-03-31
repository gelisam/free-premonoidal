{-# LANGUAGE PolyKinds, ScopedTypeVariables #-}
module TypeLevel.Axiom where

import Data.Constraint (Dict(Dict))
import Unsafe.Coerce (unsafeCoerce)


axiom :: forall a b. Dict (a ~ b)
axiom = unsafeCoerce (Dict :: Dict (a ~ a))
