{-|
Module      : Name
Description : Hierarchical names
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Hierarchical names
-}
module Name (Name,no_name,mk_name,name_append_i,name_append_s,mk_system_name_i,mk_system_name_s) where

data Name = Anonymous | AppendString Name String | AppendInteger Name Integer deriving (Eq,Ord)

show_name :: Name -> String
show_name Anonymous = ""
show_name (AppendString n s) = show_name n ++ "." ++ s
show_name (AppendInteger n i) = show_name n ++ "." ++ show(i)

instance Show Name where show n = show_name n

system_prefix = AppendString Anonymous "#_system"

mk_system_name_i i = AppendInteger system_prefix i
mk_system_name_s s = AppendString system_prefix s

no_name = Anonymous

name_append_i = AppendInteger
name_append_s = AppendString

-- | Make a name from a list of strings.
--
-- >>> mk_name ["foo","bar"]
-- .bar.foo
mk_name :: [String] -> Name
mk_name [n] = AppendString Anonymous n
mk_name (n:ns) = AppendString (mk_name ns) n
