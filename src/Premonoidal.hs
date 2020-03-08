module Premonoidal where

import Prelude hiding (id, (.))

import qualified Control.Arrow as K
import Control.Category


-- premonoidal category
class Category k => Premonoidal k where
  first  :: k a b
         -> k (a, x) (b, x)
  second :: k a b
         -> k (x, a) (x, b)
  introL :: k a ((), a)
  introR :: k a (a, ())
  elimL  :: k ((), a) a
  elimR  :: k (a, ()) a
  assocL :: k (a, (b, c))
              ((a, b), c)
  assocR :: k ((a, b), c)
              (a, (b, c))

-- symmetric premonoidal category
class Premonoidal k => Symmetric k where
  swap :: k (a, b) (b, a)

-- semicartesian premonoidal category
class Symmetric k => Semicartesian k where
  forget :: k a ()

-- cartesian premonoidal category
class Semicartesian k => Cartesian k where
  dup :: k a (a, a)


instance Premonoidal (->) where
  first  = K.first
  second = K.second
  introL a = ((), a)
  introR a = (a, ())
  elimL  ((), a) = a
  elimR  (a, ()) = a
  assocL (a, (b, c)) = ((a, b), c)
  assocR ((a, b), c) = (a, (b, c))

instance Symmetric (->) where
  swap (a, b) = (b, a)

instance Semicartesian (->) where
  forget _ = ()

instance Cartesian (->) where
  dup a = (a, a)


instance Monad m => Premonoidal (K.Kleisli m) where
  first  = K.first
  second = K.second
  introL = K.arr introL
  introR = K.arr introR
  elimL  = K.arr elimL
  elimR  = K.arr elimR
  assocL = K.arr assocL
  assocR = K.arr assocR

instance Monad m => Symmetric (K.Kleisli m) where
  swap = K.arr swap

instance Monad m => Semicartesian (K.Kleisli m) where
  forget = K.arr forget

instance Monad m => Cartesian (K.Kleisli m) where
  dup = K.arr dup
