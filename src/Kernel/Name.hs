{-|
Module      : Kernel.Name
Description : Hierarchical names
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

API for hierarchical names
-}
module Kernel.Name (
  Name
  , noName
  , mkName, mkSystemNameI, mkSystemNameS
  , nameRConsI, nameRConsS
  ) where
import Kernel.Name.Internal
