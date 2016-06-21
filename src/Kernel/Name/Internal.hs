{-|
Module      : Kernel.Name.Internal
Description : Hierarchical names
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Implementation of hierarchical names
-}
module Kernel.Name.Internal where
import Data.Text (Text, pack, unpack)

data Name = NoName | RConsText Name Text | RConsInteger Name Integer deriving (Eq,Ord)

showName :: Name -> String
showName NoName = ""
showName (RConsText n s) = showName n ++ "." ++ unpack s
showName (RConsInteger n i) = showName n ++ "." ++ show i

instance Show Name where show n = showName n

mkName :: [String] -> Name
mkName ns = mkNameCore (reverse ns) where
  mkNameCore [] = NoName
  mkNameCore (n:ns) = RConsText (mkNameCore ns) (pack n)

systemPrefix :: Name
systemPrefix = mkName ["#_system"]

mkSystemNameI :: Integer -> Name
mkSystemNameI i = RConsInteger systemPrefix i

mkSystemNameS :: String -> Name
mkSystemNameS = RConsText systemPrefix . pack

noName :: Name
noName = NoName

nameRConsS :: Name -> String -> Name
nameRConsS n = RConsText n . pack

nameRConsI :: Name -> Integer -> Name
nameRConsI = RConsInteger
