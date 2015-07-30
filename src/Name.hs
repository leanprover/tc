{-
Copyright (c) 2015 Daniel Selsam.

This file is part of the Lean reference type checker.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
-}

module Name where

data Name = Anonymous | AppendString Name String | AppendInteger Name Integer deriving (Eq,Ord)

showName :: Name -> String
showName Anonymous = ""
showName (AppendString n s) = showName n ++ "." ++ s
showName (AppendInteger n i) = showName n ++ "." ++ show(i)

instance Show Name where show n = showName n

-- TODO guarantee unique
-- TODO these are silly, need redesign
system_prefix = AppendString Anonymous "#_system"
user_prefix = AppendString Anonymous "#_user"

mk_system_name i = AppendInteger system_prefix i
mk_special_name n = AppendString system_prefix n

-- note reverse order
mk_name [n] = AppendString Anonymous n
mk_name (n:ns) = AppendString (mk_name ns) n
