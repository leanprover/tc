module Name where

data Name = Anonymous | AppendString Name String | AppendInteger Name Integer deriving (Eq,Ord)

showName :: Name -> String
showName Anonymous = ""
showName (AppendString n s) = showName n ++ "." ++ s
showName (AppendInteger n i) = showName n ++ "." ++ show(i)

instance Show Name where show n = showName n

-- TODO guarantee unique
system_prefix = AppendString Anonymous "#_system"
user_prefix = AppendString Anonymous "#_user"

mk_system_name i = AppendInteger system_prefix i
mk_name s = AppendString user_prefix s

name_append_integer n i = AppendInteger n i
name_append_string n s = AppendString n s


