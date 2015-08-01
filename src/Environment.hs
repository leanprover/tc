{-|
Module      : Environment
Description : Environments
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Environments
-}

module Environment (Declaration (..),Environment (..),CertifiedDeclaration (..),
                    mk_definition,mk_axiom,is_definition,
                    is_impredicative, is_prop_proof_irrel,
                    lookup_declaration, empty_environment, env_add,env_add_uni,
                    IntroRule (..),InductiveDecl (..),ExtElimInfo (..),CompRule (..),
                    MutualInductiveDecl (..),InductiveEnvExt (..),
                    default_inductive_env_ext,
                    ind_ext_add_inductive_info,ind_ext_add_intro_info,
                    ind_ext_add_elim, ind_ext_add_comp_rhs
                   )
where

import Name
import Level
import Expression

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import qualified Data.Maybe as Maybe

data Declaration = Declaration { decl_name :: Name,
                                 decl_level_names :: [Name],
                                 decl_type :: Expression,
                                 decl_mb_val :: Maybe Expression,
                                 decl_weight :: Integer } deriving (Eq,Show)

-- | Note: the `env` args are used to compute the declaration weights
mk_definition env name level_param_names t v =
  Declaration name level_param_names t (Just v) (1 + get_max_decl_weight env v)

mk_axiom name level_param_names t =
  Declaration name level_param_names t Nothing 0

is_definition decl = Maybe.isJust (decl_mb_val decl)

get_max_decl_weight env e = case e of
  Var var -> 0
  Local local -> get_max_decl_weight env (local_type local)
  Constant const -> maybe 0 decl_weight (lookup_declaration env (const_name const))
  Sort _ -> 0
  Lambda lam -> get_max_decl_weight env (binding_domain lam) `max` get_max_decl_weight env (binding_body lam)
  Pi pi -> get_max_decl_weight env (binding_domain pi) `max` get_max_decl_weight env (binding_body pi)
  App app -> get_max_decl_weight env (app_fn app) `max` get_max_decl_weight env (app_arg app)

-- Environments

data Environment = Environment {
  env_declarations :: Map Name Declaration,
  env_global_names :: Set Name,
  env_ind_ext :: InductiveEnvExt,
  env_quot_enabled :: Bool
  } deriving (Show)
                   
data CertifiedDeclaration = CertifiedDeclaration { cdecl_env :: Environment, cdecl_decl :: Declaration } deriving (Show)

is_impredicative :: Environment -> Bool
is_impredicative env = True -- TODO

is_prop_proof_irrel :: Environment -> Bool
is_prop_proof_irrel env = True -- TODO

lookup_declaration :: Environment -> Name -> Maybe Declaration
lookup_declaration env name = Map.lookup name (env_declarations env)

empty_environment = Environment { env_declarations = Map.empty,
                                  env_global_names = Set.empty,
                                  env_ind_ext = default_inductive_env_ext,
                                  env_quot_enabled = True }

-- TODO confirm environment is a descendent of the current one
-- or maybe make the kernel responsible for adding it
env_add :: Environment -> CertifiedDeclaration -> Environment
env_add env cdecl = case lookup_declaration env (decl_name (cdecl_decl cdecl)) of
  Nothing -> env { env_declarations = Map.insert (decl_name (cdecl_decl cdecl)) (cdecl_decl cdecl) (env_declarations env) }
  Just decl -> error "Already defined this guy, but the TypeChecker should have caught this already, will refactor later"

-- TODO return either
env_add_uni :: Environment -> Name -> Environment
env_add_uni env name = case Set.member name (env_global_names env) of
  False -> env { env_global_names = Set.insert name (env_global_names env) }
  True -> error "Already defined global universe, but interpreter should have caught this already, will refactor later"

{- Inductive extensions -}

data IntroRule = IntroRule Name Expression deriving (Show)
data InductiveDecl = InductiveDecl Name Expression [IntroRule] deriving (Show)

-- | Information used by the inductive normalizer extension
data ExtElimInfo = ExtElimInfo {
  eei_inductive_name :: Name, -- ^ name of the inductive datatype associated with eliminator
  eei_level_param_names :: [Name], -- ^ level parameter names used in computational rule
  eei_num_params :: Integer, -- ^ number of global parameters A
  eei_num_ACe :: Integer, -- ^ sum of number of global parameters A, type formers C, and minor preimises e.
  eei_num_indices :: Integer, -- ^ number of inductive datatype indices
  -- | We support K-like reduction when the inductive datatype is in Type.{0} (aka Prop), proof irrelevance is enabled,
  -- it has only one introduction rule, the introduction rule has "0 arguments".
  eei_K_target :: Bool,
  eei_dep_elim :: Bool -- ^ eei_dep_elim == true if dependent elimination is used for this eliminator
  } deriving (Show)

-- | Represents a single com
data CompRule = CompRule {
  cr_elim_name :: Name, -- ^ name of the corresponding eliminator
  cr_num_rec_nonrec_args :: Integer, -- ^ sum of number of rec_args and nonrec_args in the corresponding introduction rule.
  cr_comp_rhs :: Expression -- ^ computational rule RHS: Fun (A, C, e, b, u), (e_k_i b u v)
  } deriving (Show)

data MutualInductiveDecl = MutualInductiveDecl {
  mid_level_param_names :: [Name],
  mid_num_params :: Integer,
  mid_idecls :: [InductiveDecl]
  } deriving (Show)

data InductiveEnvExt = InductiveEnvExt {
  iext_elim_infos :: Map Name ExtElimInfo,
  iext_comp_rules :: Map Name CompRule,
  iext_ir_name_to_ind_name :: Map Name Name,
  iext_ind_infos :: Map Name MutualInductiveDecl
  } deriving (Show)

default_inductive_env_ext = InductiveEnvExt Map.empty Map.empty Map.empty Map.empty

-- Painful without Lens
-- | map every inductive type name to the mutually inductive declaration
ind_ext_add_inductive_info level_param_names num_params idecls env =
  let old_env_ind_ext = env_ind_ext env
      old_iext_ind_infos = iext_ind_infos old_env_ind_ext
      new_iext_ind_infos = 
        foldl (\ind_infos idecl@(InductiveDecl name ty intro_rules) ->
                Map.insert name (MutualInductiveDecl level_param_names num_params idecls) ind_infos) old_iext_ind_infos idecls
      new_env_ind_ext = old_env_ind_ext { iext_ind_infos = new_iext_ind_infos } 
  in
   env { env_ind_ext = new_env_ind_ext }
  
ind_ext_add_intro_info ir_name ind_name env =
  let old_env_ind_ext = env_ind_ext env
      old_m = iext_ir_name_to_ind_name old_env_ind_ext
  in
   env { env_ind_ext = old_env_ind_ext { iext_ir_name_to_ind_name = Map.insert ir_name ind_name old_m } }

ind_ext_add_elim elim_name ind_name level_param_names num_params num_ACe num_indices is_K_target dep_elim env =
  let old_env_ind_ext = env_ind_ext env
      old_m = iext_elim_infos old_env_ind_ext
      new_elim_info = ExtElimInfo ind_name level_param_names num_params num_ACe num_indices is_K_target dep_elim 
  in
   env { env_ind_ext = old_env_ind_ext { iext_elim_infos = Map.insert elim_name new_elim_info old_m } }

ind_ext_add_comp_rhs ir_name elim_name num_rec_args_nonrec_args rhs env =
  let old_env_ind_ext = env_ind_ext env
      old_m = iext_comp_rules old_env_ind_ext
      new_comp_rule = CompRule elim_name num_rec_args_nonrec_args rhs
  in
   env { env_ind_ext = old_env_ind_ext { iext_comp_rules = Map.insert ir_name new_comp_rule old_m } }
