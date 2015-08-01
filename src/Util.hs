{-|
Module      : Util
Description : Utilities
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

-}
module Util (assert) where

-- | Throw an error of the condition does not hold.
assert :: Bool -> String -> a -> a
assert False s x = error s
assert _  _ x = x
