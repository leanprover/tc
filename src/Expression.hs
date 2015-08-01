{-|
Module      : Expression
Description : Expressions
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Expressions
-}
module Expression (Expression (..),
                   VarData (..), LocalData (..), ConstantData (..), SortData (..), AppData (..), BindingData (..),
                   BinderInfo (..),
                   mk_constant,mk_local,mk_var,mk_sort,mk_lambda,mk_pi,mk_app,
                   mk_lambda_anon,mk_pi_anon,mk_local_data,mk_local_data_full,
                   instantiate,instantiate_seq,instantiate_univ_params,
                   abstract_pi,abstract_pi_seq,abstract_lambda_seq,
                   has_local,has_free_vars,closed,
                   get_operator,get_app_args,get_app_op_args,body_of_lambda,
                   mk_Prop,mk_app_seq,
                   find_in_expr,
                   maybe_constant)
where

import Control.Monad

import Name
import Level
import qualified Data.Maybe as Maybe
import Data.List (findIndex,genericTake,genericLength,genericIndex)
import Debug.Trace

data BinderInfo = BinderDefault | BinderImplicit | BinderStrict | BinderClass deriving (Eq,Show,Ord)
data ExprCache = ExprCache { cache_has_local :: Bool,
                             cache_has_param_univ :: Bool,
                             cache_weight :: Integer,
                             cache_free_var_range :: Integer } deriving (Eq,Show,Ord)

data VarData = VarData { var_idx :: Integer } deriving (Eq,Show,Ord)

data LocalData = LocalData { local_name :: Name ,
                             local_pp_name :: Name,
                             local_type :: Expression,
                             local_info :: BinderInfo,
                             local_cache :: ExprCache } deriving (Eq,Ord)

showLocal local = "(Local: <" ++ show (local_name local) ++ "> " ++ show (local_type local) ++ ")"
instance Show LocalData where show e = showLocal e


data SortData = SortData { sort_level :: Level } deriving (Eq,Show,Ord)

data ConstantData = ConstantData { const_name :: Name , const_levels :: [Level] } deriving (Eq,Show,Ord)

data AppData = AppData { app_fn :: Expression, app_arg :: Expression, app_cache :: ExprCache  } deriving (Eq,Show,Ord)

data BindingData = BindingData { is_pi :: Bool,
                                 binding_name :: Name,
                                 binding_domain :: Expression,
                                 binding_body :: Expression,
                                 binding_info :: BinderInfo,
                                 binding_cache :: ExprCache } deriving (Eq,Show,Ord)

data Expression = Var VarData
                | Local LocalData
                | Sort SortData 
                | Constant ConstantData
                | Lambda BindingData 
                | Pi BindingData 
                | App AppData
                deriving (Eq,Ord)

show_expression :: Expression -> String
show_expression e = case e of
  Var var -> "#" ++ show (var_idx var)
  Local local -> show local
  Sort sort -> "(Sort: " ++ show (sort_level sort) ++ ")"
  Constant const -> "'" ++ show (const_name const) ++ " " ++ show (const_levels const) ++ "'" -- "(Constant: " ++ show (const_name const) ++ ")"
  Lambda lam -> "(Lambda: " ++ show (binding_domain lam) ++ " ==> " ++ show (binding_body lam) ++ ")"
  Pi pi -> "(Pi: " ++ show (binding_domain pi) ++ " -> " ++ show (binding_body pi) ++ ")"
  App app -> let (f,args) = (get_operator e,get_app_args e) in "(App: " ++ show f ++ " @ " ++ show args ++ ")"

instance Show Expression where show e = show_expression e

-- Helpers

has_local e = case e of
  Var _ -> False
  Local _ -> True
  Sort _ -> False
  Constant _ -> False
  Lambda lam -> cache_has_local $ binding_cache lam
  Pi pi -> cache_has_local $ binding_cache pi
  App app -> cache_has_local $ app_cache app

get_free_var_range e = case e of
  Var var -> 1 + var_idx var
  Local local -> cache_free_var_range $ local_cache local
  Constant _ -> 0
  Sort _ -> 0
  Lambda lam -> cache_free_var_range $ binding_cache lam
  Pi pi -> cache_free_var_range $ binding_cache pi
  App app -> cache_free_var_range $ app_cache app
  
has_free_vars e = get_free_var_range e > 0

expr_has_param_univ e = case e of
  Var var -> False
  Local local -> cache_has_param_univ $ local_cache local
  Constant const -> any (==True) (map has_param (const_levels const))
  Sort sort -> has_param (sort_level sort)
  Lambda lam -> cache_has_param_univ $ binding_cache lam
  Pi pi -> cache_has_param_univ $ binding_cache pi
  App app -> cache_has_param_univ $ app_cache app

expr_weight e = case e of
  Var var -> 1
  Local local -> cache_weight $ local_cache local
  Constant const -> 1
  Sort _ -> 1
  Lambda lam -> cache_weight $ binding_cache lam
  Pi pi -> cache_weight $ binding_cache pi
  App app -> cache_weight $ app_cache app

closed e = not $ has_free_vars e


get_operator :: Expression -> Expression
get_operator e = case e of
  App app -> get_operator (app_fn app)
  _ -> e

get_app_op_args e = (get_operator e,get_app_args e)

get_app_args :: Expression -> [Expression]
get_app_args e = get_app_args_core e [] where
  get_app_args_core e args =
    case e of
      App app -> get_app_args_core (app_fn app) (app_arg app : args)
      _ -> args




-- Makers
mk_sort l = Sort (SortData l)
mk_var v_idx = Var (VarData v_idx)

mk_Prop = mk_sort mk_zero
mk_Type = mk_sort mk_level_one
mk_Type2 = mk_sort mk_level_two

mk_constant name levels = Constant (ConstantData name levels)


mk_app fn arg = App (AppData fn arg (ExprCache
                                     (has_local fn || has_local arg)
                                     (expr_has_param_univ fn || expr_has_param_univ arg)
                                     (expr_weight fn + expr_weight arg + 1)
                                     (max (get_free_var_range fn) (get_free_var_range arg))))

mk_app_seq fn [] = fn
mk_app_seq fn (arg:args) = mk_app_seq (mk_app fn arg) args

mk_binding is_pi name domain body binfo = 
  let ecache = (ExprCache
                (has_local domain || has_local body)
                (expr_has_param_univ domain || expr_has_param_univ body)
                (expr_weight domain + expr_weight body + 1)
                (max (get_free_var_range domain) (get_free_var_range body - 1))) in
  case is_pi of
    True -> Pi (BindingData is_pi name domain body binfo ecache)
    False -> Lambda (BindingData is_pi name domain body binfo ecache)

mk_pi = mk_binding True
mk_pi_anon domain body = mk_pi no_name domain body BinderDefault

mk_lambda = mk_binding False
mk_lambda_anon domain body = mk_lambda no_name domain body BinderDefault

mk_local_data name pp_name ty = mk_local_data_full name pp_name ty BinderDefault
mk_local_data_full name pp_name ty binfo = LocalData name pp_name ty binfo
                                           (ExprCache True (expr_has_param_univ ty) 1 (get_free_var_range ty))

mk_local name pp_name ty binfo = Local $ mk_local_data_full name pp_name ty binfo


-- Replace
type Offset = Integer
type ReplaceFn = (Expression -> Offset -> Maybe Expression)
replace_in_expr :: ReplaceFn -> Expression -> Expression
replace_in_expr f t = replace_in_expr_core f t 0

replace_in_expr_core :: ReplaceFn -> Expression -> Offset -> Expression
replace_in_expr_core f t offset =
  case f t offset of
    Just t0 -> t0
    Nothing ->
      case t of
        Local local -> update_local_type local (replace_in_expr_core f (local_type local) offset)
        App app -> update_app app (replace_in_expr_core f (app_fn app) offset)
                   (replace_in_expr_core f (app_arg app) offset)
        Lambda lam -> update_binding lam (replace_in_expr_core f (binding_domain lam) offset)
                      (replace_in_expr_core f (binding_body lam) (1+offset))
        Pi pi -> update_binding pi (replace_in_expr_core f (binding_domain pi) offset)
                      (replace_in_expr_core f (binding_body pi) (1+offset))
        _ -> t

-- ForEach

        
-- Find
type FindFn = (Expression -> Offset -> Bool)
find_in_expr :: FindFn -> Expression -> Maybe Expression
find_in_expr f t = find_in_expr_core f t 0

find_in_expr_core :: FindFn -> Expression -> Offset -> Maybe Expression
find_in_expr_core f t offset =
  if f t offset then Just t else
    case t of
      Local local -> find_in_expr_core f (local_type local) offset
      App app -> find_in_expr_core f (app_fn app) offset `mplus` find_in_expr_core f (app_arg app) offset
      Lambda lam -> find_in_expr_core f (binding_domain lam) offset `mplus` find_in_expr_core f (binding_body lam) (offset+1)
      Pi pi -> find_in_expr_core f (binding_domain pi) offset `mplus` find_in_expr_core f (binding_body pi) (offset+1)
      _ -> Nothing

-- Instantiate

instantiate_seq e substs = replace_in_expr (instantiate_fn substs) e
  where instantiate_fn substs e offset
          | offset >= get_free_var_range e = Just e
        instantiate_fn substs (Var var) offset
          | var_idx var >= offset && var_idx var < offset + (genericLength substs) =
            Just $ lift_free_vars (genericIndex substs (var_idx var - offset)) offset
          | var_idx var > offset = Just $ mk_var (var_idx var - (genericLength substs))
        instantiate_fn _ _ _ = Nothing        

instantiate e subst = instantiate_seq e [subst]

-- Lift free vars

lift_free_vars_fn :: Offset -> ReplaceFn
lift_free_vars_fn shift e offset
  | offset >= get_free_var_range e = Just e

lift_free_vars_fn shift (Var var) offset
  | var_idx var >= offset = Just $ mk_var (var_idx var + shift)

lift_free_vars_fn _ _ _ = Nothing

lift_free_vars e shift = replace_in_expr (lift_free_vars_fn shift) e

-- Instantiate universe params
instantiate_univ_params_fn :: [Name] -> [Level] -> ReplaceFn
instantiate_univ_params_fn level_param_names levels e _
  | not (expr_has_param_univ e) = Just e

instantiate_univ_params_fn level_param_names levels (Constant const) _ =
  Just $ update_constant const (map (instantiate_level level_param_names levels) (const_levels const))

instantiate_univ_params_fn level_param_names levels (Sort sort) _ =
  Just $ update_sort sort (instantiate_level level_param_names levels (sort_level sort))

instantiate_univ_params_fn _ _ _ _ = Nothing

instantiate_univ_params e level_names levels =
  let ret = replace_in_expr (instantiate_univ_params_fn level_names levels) e in
  -- trace ("instantiate\n\n" ++ show e ++ "\n\n" ++ show level_names ++ "\n\n" ++ show levels ++ "\n\n" ++ show ret ++ "\n\n\n")
  ret


-- Abstract locals

abstract_pi local body = abstract_binding_seq True [local] body
abstract_lambda local body = abstract_binding_seq False [local] body

abstract_pi_seq locals body = abstract_binding_seq True locals body
abstract_lambda_seq locals body = abstract_binding_seq False locals body

abstract_binding_seq is_pi locals body =
  let abstract_body = abstract_locals locals body
      abstract_types = map (\(local,i) -> abstract_locals (genericTake i locals) (local_type local)) (zip locals [0..])
  in
   foldr (\(abstract_type,local) new_body -> mk_binding is_pi (local_name local) abstract_type new_body (local_info local))
   abstract_body (zip abstract_types locals)

{- TODO use = go expr where ... -} 
abstract_locals_fn :: [LocalData] -> ReplaceFn
abstract_locals_fn locals e offset
  | not (has_local e) = Just e

abstract_locals_fn locals e@(Local l) offset =
  case findIndex (\local -> local_name local == local_name l) locals of
    Nothing -> Just e
    Just idx -> Just (mk_var $ offset + (toInteger (length locals - 1 - idx)))

abstract_locals_fn _ _  _ = Nothing
                            
abstract_locals locals body = replace_in_expr (abstract_locals_fn locals) body

-- Updaters
-- TODO check equality first

update_local_type :: LocalData -> Expression -> Expression
update_local_type local new_type = mk_local (local_name local) (local_pp_name local) new_type (local_info local)

update_binding :: BindingData -> Expression -> Expression -> Expression
update_binding bind new_domain new_body =
  mk_binding (is_pi bind) (binding_name bind) new_domain new_body (binding_info bind)

update_app :: AppData -> Expression -> Expression -> Expression
update_app app new_fn new_arg = mk_app new_fn new_arg

update_constant const levels = mk_constant (const_name const) levels
update_sort sort level = mk_sort level

body_of_lambda e = case e of
  Lambda lam -> body_of_lambda (binding_body lam)
  _ -> e
  
is_constant (Constant _) = True
is_constant _ = False

maybe_constant (Constant c) = Just c
maybe_constant _ = Nothing

has_constant_with_name e name = Maybe.isJust (find_in_expr f e) where
  f (Constant c) _ | (const_name c == name) = True
  f _ _ = False
