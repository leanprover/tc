module Util where

assert :: Bool -> String -> a -> a
assert False s x = error s
assert _  _ x = x
