module Environment where

import Name
import Level
import Expression

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import qualified Data.Maybe as Maybe

-- Declarations

data Declaration = Declaration { decl_name :: Name,
                                 decl_level_names :: [Name],
                                 decl_type :: Expression,
                                 decl_is_thm :: Bool,
                                 decl_mb_val :: Maybe Expression,
                                 decl_weight :: Integer } deriving (Eq,Show)

-- The `env` args are used to compute the declaration weights
mk_definition env name level_param_names t v =
  Declaration name level_param_names t False (Just v) (1 + get_max_decl_weight env v)

mk_theorem env name level_param_names t v =
  Declaration name level_param_names t True (Just v) (1 + get_max_decl_weight env v)

mk_axiom name level_param_names t =
  Declaration name level_param_names t True Nothing 0
  
mk_constant_assumption name level_param_names t =
  Declaration name level_param_names t False Nothing 0

-- These are a littel confusing
is_definition d = Maybe.isJust $ decl_mb_val d
is_constant_assumption d = not $ is_definition d
is_axiom d = is_constant_assumption d && decl_is_thm d
is_theorem d = is_definition d && decl_is_thm d

-- TODO not that ugly but could use a more generic fold operation
get_max_decl_weight env e = case e of
  Var var -> 0
  Local local -> get_max_decl_weight env (local_type local)
  Constant const -> maybe 0 decl_weight (lookup_declaration env (const_name const))
  Sort _ -> 0
  Lambda lam -> get_max_decl_weight env (binding_domain lam) `max` get_max_decl_weight env (binding_body lam)
  Pi pi -> get_max_decl_weight env (binding_domain pi) `max` get_max_decl_weight env (binding_body pi)
  App app -> get_max_decl_weight env (app_fn app) `max` get_max_decl_weight env (app_arg app)

-- Environments

data NormalizerExtension a = NormalizerExtension {
  reduce :: Environment -> [Name] -> a -> Expression -> Maybe Expression ,
  is_recursor :: Environment -> Name -> Bool ,
  is_builtin :: Environment -> Name -> Bool
  }


instance Show (NormalizerExtension a) where show n = "<norm_ext>"


-- TODO
data QuotientEnvExt = QuotientEnvExt { } deriving (Show)

-- TODO
data InductiveEnvExt = InductiveEnvExt { } deriving (Show)

data EnvironmentHeader = EnvironmentHeader {
  eh_prop_proof_irrel :: Bool,
  eh_eta :: Bool,
  eh_impredicative :: Bool,
  
  eh_norm_exts :: (Maybe (NormalizerExtension QuotientEnvExt), Maybe (NormalizerExtension InductiveEnvExt))
  } deriving (Show)
  
data Environment = Environment {
  env_header :: EnvironmentHeader ,
  env_parent :: Maybe Environment , -- TODO does GHC optimize this appropriately?
  env_depth :: Integer ,
  env_declarations :: Map Name Declaration,
  env_global_names :: [Name],
  env_quot_ext :: QuotientEnvExt,
  env_ind_ext :: InductiveEnvExt
  } deriving (Show)
                   
  

data CertifiedDeclaration = CertifiedDeclaration { cdecl_env :: Environment, cdecl_decl :: Declaration } deriving (Show)

lookup_declaration :: Environment -> Name -> Maybe Declaration
lookup_declaration env name = Map.lookup name (env_declarations env)

is_opaque decl = False

default_env_header = EnvironmentHeader { eh_prop_proof_irrel = True, eh_eta = True, eh_impredicative = True, eh_norm_exts = (Nothing,Nothing) }
empty_environment = Environment { env_header = default_env_header, env_parent = Nothing, env_depth = 0, env_declarations = Map.empty,
                                  env_global_names = [], env_quot_ext = QuotientEnvExt, env_ind_ext = InductiveEnvExt }

-- TODO confirm environment is a descendent of the current one
-- or maybe make the kernel responsible for adding it
env_add :: Environment -> CertifiedDeclaration -> Environment
env_add env cdecl = case lookup_declaration env (decl_name (cdecl_decl cdecl)) of
  Nothing -> env { env_declarations = Map.insert (decl_name (cdecl_decl cdecl)) (cdecl_decl cdecl) (env_declarations env) }
  Just decl -> error "Already defined this guy, but the TypeChecker should have caught this already, will refactor later"

-- TODO throw error if duplicated
env_add_uni :: Environment -> Name -> Environment
env_add_uni env name = env { env_global_names = name : (env_global_names env) }
