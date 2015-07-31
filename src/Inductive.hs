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

module Inductive where

import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe

import Util
import Name
import Level
import Expression

import Environment


import qualified TypeChecker as TypeChecker

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import Data.List (genericIndex,genericLength,genericTake,genericDrop,genericSplitAt)
import qualified Data.Maybe as Maybe

import Debug.Trace


data InductiveDeclError = NoInductiveTypeDecls
                        | ParamsOfInductiveTypesMustMatch
                        | NumParamsMismatchInInductiveDecl Integer Integer
                        | ArgDoesNotMatchInductiveParameters Integer Name
                        | UniLevelOfArgTooBig Integer Name
                        | OneInPropAllInProp 
                        | NonRecArgAfterRecArg Integer Name
                        | InvalidRecArg Integer Name
                        | InvalidReturnType Name
                        | NonPosOccurrence Integer Name
                        | NonValidOccurrence Integer Name
                        | TypeCheckError TypeChecker.TypeError String
                        deriving (Eq,Show)

-- Will be used for State monad
-- TODO split into State/Reader?
-- Note: Maybe a placeholder until we fill in the slot
-- (will probably assume `Just` once we set it)
data ElimInfo = ElimInfo {
  m_C :: LocalData, -- type former constant
  m_indices :: [LocalData], --local constant for each index
  m_major_premise :: LocalData, -- major premise for each inductive decl
  m_minor_premises :: [LocalData] -- minor premise for each introduction rule
} deriving (Eq,Show)


data AddInductiveData = AddInductiveData {
  m_env :: Environment ,
  m_level_names :: [Name],
  m_num_params :: Integer,
  m_decls :: [InductiveDecl],
  m_is_not_zero :: Bool,
  m_levels :: [Level],
  m_next_id :: Integer, 
  m_elim_level :: Maybe Level,
  m_dep_elim :: Bool,

  m_param_consts :: [LocalData], -- local constants used to represent global parameters
  m_it_levels :: [Level], -- the levels for each inductive datatype in [m_decls]
  m_it_consts :: [ConstantData], -- the constants for each inductive datatype in [m_decls]
  m_it_num_args :: [Integer], -- total number of arguments (params + indices) for each inductive datatype in m_decls

  m_elim_infos :: [ElimInfo],
  m_K_target :: Bool
}

mk_add_inductive_data env level_names num_params decls = AddInductiveData { 
  m_env = env,
  m_level_names = level_names,
  m_num_params = num_params,
  m_decls = decls,
  m_is_not_zero = False,
  m_levels = map LevelParam level_names,
  m_next_id = 0, -- TODO
  m_elim_level = Nothing,
  m_dep_elim = False,
  m_param_consts = [],
  m_it_levels = [],
  m_it_consts = [],
  m_it_num_args = [],
  m_elim_infos = [],
  m_K_target = False
  }

gensym = do
  ind_data <- get
  put $ ind_data { m_next_id = (m_next_id ind_data + 1) }
  return $ m_next_id ind_data

mk_fresh_name = do
  id <- gensym
  return $ AppendInteger (mk_system_name id) id

add_inductive :: Environment -> [Name] -> Integer -> [InductiveDecl] -> Either InductiveDeclError Environment
add_inductive env level_names num_params decls =
  let (a,s) = runState (runExceptT add_inductive_core) (mk_add_inductive_data env level_names num_params decls) in
  case a of
    Left err -> Left err
    Right () -> Right $ m_env s
  
type AddInductiveMethod = ExceptT InductiveDeclError (State AddInductiveData)

ind_run ind_fn env level_names num_params decls = runState (runExceptT ind_fn) (mk_add_inductive_data env level_names num_params decls)
ind_exec ind_fn env level_names num_params decls = execState (runExceptT ind_fn) (mk_add_inductive_data env level_names num_params decls)
ind_eval ind_fn env level_names num_params decls = evalState (runExceptT ind_fn) (mk_add_inductive_data env level_names num_params decls)

add_inductive_core :: AddInductiveMethod ()
add_inductive_core = do
  check_inductive_types
  declare_inductive_types
  check_intro_rules
  declare_intro_rules
  declare_elim_rules
  mk_comp_rules_rhs


{- Check if the type of datatypes is well typed, all inductive datatypes have the same parameters, and the number of parameters match the argument num_params. This method also populates the fields m_param_consts, m_it_levels, m_it_consts. -}
check_inductive_types :: AddInductiveMethod ()
check_inductive_types = do
  ind_data <- get
  case m_decls ind_data of
    [] -> throwE NoInductiveTypeDecls
    decl : decls -> do check_inductive_decl True decl
                       mapM_ (check_inductive_decl False) decls

  
check_inductive_decl :: Bool -> InductiveDecl -> AddInductiveMethod ()
check_inductive_decl first (InductiveDecl name ty intro_rules) = do
  level_names <- gets m_level_names
  check_type ty level_names
  check_inductive_decl_core first 0 name ty 

mk_local_for :: BindingData -> AddInductiveMethod LocalData
mk_local_for bind = do
  next_id <- gensym
  return $ mk_local_data_full (mk_system_name next_id) (binding_name bind) (binding_domain bind) (binding_info bind)

ind_assert b err = if b then return () else throwE err

check_inductive_decl_core :: Bool -> Integer -> Name -> Expression -> AddInductiveMethod ()
check_inductive_decl_core first i name ty = do
  num_params <- gets m_num_params
  case ty of
    Pi pi | i < num_params ->
      case first of
        True -> do local <- mk_local_for pi
                   modify (\ind_data -> ind_data { m_param_consts = m_param_consts ind_data ++ [local] })
                   check_inductive_decl_core first (i+1) name (instantiate (binding_body pi) (Local local))
        False -> do param_consts <- gets m_param_consts
                    local <- return $ genericIndex param_consts i
                    is_eq <- is_def_eq (binding_domain pi) (local_type local)
                    if is_eq
                      then check_inductive_decl_core first (i+1) name (instantiate (binding_body pi) (Local local))
                      else throwE ParamsOfInductiveTypesMustMatch
    Pi pi -> check_inductive_decl_core first (i+1) name (binding_body pi)
    _ -> do num_params <- gets m_num_params
            ind_assert (i >= num_params) $ NumParamsMismatchInInductiveDecl i num_params
            modify (\ind_data -> ind_data { m_it_num_args = m_it_num_args ind_data ++ [i] })
            sort <- ensure_sort ty
            env <- gets m_env
            if is_impredicative env then handle_impredicative_env first sort else return ()
            modify (\ind_data -> ind_data { m_it_levels = m_it_levels ind_data ++ [sort_level sort] })
            modify (\ind_data -> ind_data { m_it_consts = m_it_consts ind_data ++ [ConstantData name (m_levels ind_data)] })

-- Needs to check whether env is impredicative
handle_impredicative_env :: Bool -> SortData -> AddInductiveMethod ()
handle_impredicative_env True sort = modify (\ind_data -> ind_data { m_is_not_zero = is_definitely_not_zero (sort_level sort) })
handle_impredicative_env False sort = do
  is_not_zero <- gets m_is_not_zero
  ind_assert (is_definitely_not_zero (sort_level sort) == is_not_zero) OneInPropAllInProp 


-- Add all datatype declarations to environment.
declare_inductive_types :: AddInductiveMethod ()
declare_inductive_types = do
  gets m_decls >>= mapM_ (\decl -> do
                             cdecl <- certify_ideclaration decl
                             update_m_env (flip env_add cdecl))
  ext_add_inductive_info
  


{- Check if
   - all introduction rules start with the same parameters
   - the type of all arguments (which are not datatype global params) live in universes <= level of the corresponding datatype
   - all inductive datatype occurrences are positive
   - all introduction rules are well typed

   Note: this method must be executed after declare_inductive_types
-}

check_intro_rules :: AddInductiveMethod ()
check_intro_rules = gets m_decls >>= check_intro_rules_core 0

check_intro_rules_core :: Integer -> [InductiveDecl] -> AddInductiveMethod ()
check_intro_rules_core i decls =
  case decls of
    [] -> return ()
    (InductiveDecl _ _ intro_rules):ds -> mapM_ (check_intro_rule i) intro_rules >> check_intro_rules_core (i+1) ds

{-
  Check the intro_rule ir of the given inductive decl. d_idx is the position of d in m_decls.
  See check_intro_rules.
-}
check_intro_rule :: Integer -> IntroRule -> AddInductiveMethod ()
check_intro_rule d_idx (IntroRule name ty) = do
  level_names <- gets m_level_names
  check_type ty level_names
  check_intro_rule_core d_idx 0 False name ty

check_intro_rule_core d_idx param_num found_rec name ty =
  case ty of
    Pi pi -> do num_params <- gets m_num_params
                param_consts <- gets m_param_consts
                if param_num < num_params
                  then do local <- return $ genericIndex param_consts param_num
                          is_eq <- is_def_eq (binding_domain pi) (local_type local)
                          ind_assert is_eq (ArgDoesNotMatchInductiveParameters param_num name)
                          check_intro_rule_core d_idx (param_num+1) found_rec name (instantiate (binding_body pi) (Local local))
                  else do sort <- ensure_type (binding_domain pi)
                          {- the sort is ok IF
                             1. its level is <= inductive datatype level, OR
                             2. m_env is impredicative and inductive datatype is at level 0 -}
                          it_level <- liftM (flip genericIndex d_idx . m_it_levels) get
                          env <- gets m_env
                          ind_assert (sort_level sort <= it_level || (is_zero it_level && is_impredicative env))
                            (UniLevelOfArgTooBig param_num name)
                          domain_ty <- whnf (binding_domain pi)
                          check_positivity domain_ty name param_num
                          is_rec <- is_rec_argument domain_ty
                          ind_assert (not found_rec || is_rec) (NonRecArgAfterRecArg param_num name)
                          ty <- if is_rec
                                then ind_assert (closed (binding_body pi)) (InvalidRecArg param_num name) >> return (binding_body pi)
                                else mk_local_for pi >>= return . instantiate (binding_body pi) . Local
                          check_intro_rule_core d_idx (param_num+1) is_rec name ty
    _ -> is_valid_it_app_idx ty d_idx >>= flip ind_assert (InvalidReturnType name)

-- Check if ty contains only positive occurrences of the inductive datatypes being declared.
check_positivity ty name param_num = do
  it_occ <- has_it_occ ty
  if not it_occ then return () else
    case ty of
      Pi pi -> do it_occ <- has_it_occ (binding_domain pi)
                  ind_assert (not it_occ) (NonPosOccurrence param_num name)
                  check_positivity (binding_body pi) name param_num
      _ -> do
        -- trace ("check_positivity_body: " ++ show ty) (return ())
        is_valid_it_app ty >>= flip ind_assert (NonValidOccurrence param_num name)

-- Return true if ty does not contain any occurrence of a datatype being declared.
has_it_occ ty = do
  it_consts <- gets m_it_consts
  return . Maybe.isJust $ find_in_expr (\e _ -> case e of
                            Constant const -> const_name const `elem` (map const_name it_consts)
                            _ -> False) ty
    
{- Return some(d_idx) iff \c t is a recursive argument, \c d_idx is the index of the recursive inductive datatype.
   Return none otherwise. -}
is_rec_argument ty = do
  ty <- whnf ty
  case ty of
    Pi pi -> mk_local_for pi >>= is_rec_argument . (instantiate (binding_body pi)) . Local
    _ -> is_valid_it_app ty

is_valid_it_app_idx :: Expression -> Integer -> AddInductiveMethod Bool
is_valid_it_app_idx ty d_idx = do
  it_const <- liftM (flip genericIndex d_idx . m_it_consts) get
  num_args <- liftM (flip genericIndex d_idx . m_it_num_args) get
  (fn,args) <- return $ (get_operator ty,get_app_args ty)
  is_eq <- is_def_eq fn (Constant it_const)
  param_consts <- gets m_param_consts
  return $ is_eq && genericLength args == num_args && all (uncurry (==)) (zip args (map Local param_consts))

is_valid_it_app :: Expression -> AddInductiveMethod Bool
is_valid_it_app ty = do
  valid_it_app <- runExceptT (is_valid_it_app_core ty)
  case valid_it_app of
    Left d_idx -> return True
    Right () -> return False

get_valid_it_app_idx ty = do
  valid_it_app <- runExceptT (is_valid_it_app_core ty)
  case valid_it_app of
    Left d_idx -> return $ Just d_idx
    Right () -> return $ Nothing
  
is_valid_it_app_core :: Expression -> ExceptT Integer AddInductiveMethod ()
is_valid_it_app_core ty = do
  it_consts <- gets m_it_consts
  mapM_ (\d_idx -> do is_valid <- lift $ is_valid_it_app_idx ty d_idx
                      if is_valid then throwE d_idx else return ())
    [0..(genericLength it_consts - 1)]

-- Add all introduction rules (aka constructors) to environment.
declare_intro_rules =
  gets m_decls >>=
  mapM_ (\(InductiveDecl it_name _ intro_rules) -> do
            mapM_ (\(IntroRule ir_name ty) -> do
                      level_names <- gets m_level_names
                      cdecl <- certify_declaration ir_name level_names ty
                      update_m_env (flip env_add cdecl)
                      -- trace ("(" ++ show ir_name ++ "): " ++ show ty) (return ())
                      ext_add_intro_info ir_name it_name)
              intro_rules)

-- Declare the eliminator/recursor for each datatype.
declare_elim_rules = do
  init_dep_elim
  init_elim_level
  init_elim_info
  decls <- gets m_decls
  mapM_ (uncurry declare_elim_rule) (zip decls [0..])

init_dep_elim = do
  env <- gets m_env
  it_levels <- gets m_it_levels
  case it_levels of
    it_level : _ ->
      modify (\ind_data -> ind_data { m_dep_elim = not (is_impredicative env && prop_proof_irrel env && is_zero it_level) })

-- Return true if type formers C in the recursors can only map to Type.{0}
elim_only_at_universe_zero = do
  only_at_zero <- runExceptT elim_only_at_universe_zero_core
  case only_at_zero of
    Left b -> return b
    Right () -> return False

elim_only_at_universe_zero_core :: ExceptT Bool AddInductiveMethod ()
elim_only_at_universe_zero_core = do
  env <- gets m_env
  decls <- gets m_decls
  is_not_zero <- gets m_is_not_zero
  if is_impredicative env && is_not_zero then throwE False else return ()
  case decls of
    d1:d2:_ -> throwE True
    [(InductiveDecl _ _ [])] -> throwE False
    [(InductiveDecl _ _ (_:_:_))] -> throwE True
    [(InductiveDecl _ _ [(IntroRule name ty)])] -> do
      {- We have only one introduction rule, the final check is, the type of each argument that is not a parameter:
          1- It must live in Type.{0}, *OR*
          2- It must occur in the return type. (this is essentially what is called a non-uniform parameter in Coq).
             We can justify 2 by observing that this information is not a *secret* it is part of the type.
             By eliminating to a non-proposition, we would not be revealing anything that is not already known. -}
      (ty,args_to_check) <- lift $ check_condition1 ty 0
      result_args <- return $ get_app_args ty
      mapM_ (\arg_to_check -> if not (arg_to_check `elem` result_args) then throwE True else return ())
        (map Local args_to_check)

check_condition1 :: Expression -> Integer -> AddInductiveMethod (Expression,[LocalData])
check_condition1 (Pi pi) param_num = do
  local <- mk_local_for pi
  body <- return $ instantiate (binding_body pi) (Local local)
  (ty,rest) <- check_condition1 body (param_num+1)
  num_params <- gets m_num_params
  if param_num >= num_params
    then do sort <- ensure_type (binding_domain pi)
            return $ if not (is_zero (sort_level sort)) then (ty,local : rest) else (ty,rest)
    else return (ty,rest)
            
check_condition1 ty _ = return (ty,[])

-- Initialize m_elim_level.
init_elim_level = do
  only_at_zero <- elim_only_at_universe_zero
  if only_at_zero
    then modify (\ind_data -> ind_data { m_elim_level = Just mk_level_zero })
    else modify (\ind_data -> ind_data { m_elim_level = Just (mk_level_param (mk_special_name "elim_level")) })

{-data ElimInfo = ElimInfo {
  m_C :: Maybe Expression, -- type former constant
  m_indices :: [Expression], --local constant for each index
  m_major_premise :: Maybe Expression, -- major premise for each inductive decl
  m_minor_premises :: [Expression], -- minor premise for each introduction rule
-}

init_elim_info = do
  decls <- gets m_decls
  mapM_ (uncurry populate_C_indices_major) (zip decls [0..])
  mapM_ (uncurry populate_minor_premises) (zip decls [0..])

populate_C_indices_major :: InductiveDecl -> Integer -> AddInductiveMethod ()
populate_C_indices_major (InductiveDecl name ty intro_rules) d_idx = do
  (indices,body) <- build_indices ty 0
  fresh_name_major <- mk_fresh_name
  it_consts <- gets m_it_consts
  param_consts <- gets m_param_consts
  major_premise <- return $ mk_local_data fresh_name_major (mk_name ["n"])
                   (mk_app_seq (mk_app_seq
                                (Constant $ genericIndex it_consts d_idx) (map Local param_consts))
                    (map Local indices))
  elim_level <- gets m_elim_level
  c_ty <- return $ mk_sort (Maybe.fromJust elim_level)
  dep_elim <- gets m_dep_elim
  c_ty <- return $ if dep_elim then abstract_pi major_premise c_ty else c_ty
  c_ty <- return $ abstract_pi_seq indices c_ty
  num_its <- liftM (genericLength . m_decls) get
  c_name <- return $ if num_its > 1 then AppendInteger (mk_name ["C"]) d_idx else mk_name ["C"]
  fresh_name_C <- mk_fresh_name
  c <- return $ mk_local_data fresh_name_C c_name c_ty
  modify (\ind_data -> ind_data { m_elim_infos = (m_elim_infos ind_data) ++ [ElimInfo c indices major_premise []] })

build_indices :: Expression -> Integer -> AddInductiveMethod ([LocalData],Expression)
build_indices (Pi pi) param_num = do
  num_params <- gets m_num_params  
  use_param <- return $ param_num < num_params
  local <- if use_param 
           then liftM (flip genericIndex param_num . m_param_consts) get
           else mk_local_for pi
  (indices,body) <- build_indices (instantiate (binding_body pi) (Local local)) (param_num+1)
  if use_param
    then return (indices,body)
    else return (local:indices,body)

build_indices ty param_num = return ([],ty)

populate_minor_premises :: InductiveDecl -> Integer -> AddInductiveMethod ()
populate_minor_premises (InductiveDecl name ty intro_rules) d_idx = do
  env <- gets m_env
  it_level <- liftM (flip genericIndex d_idx . m_it_levels) get
  -- A declaration is target for K-like reduction when it has one intro,
  -- the intro has 0 arguments, proof irrelevance is enabled, and it is a proposition.
  modify (\ind_data -> ind_data { m_K_target = prop_proof_irrel env && is_zero it_level && length intro_rules == 1 })
  -- In the populate_minor_premises_intro_rule we check if the intro rule has 0 arguments.
  mapM_ (populate_minor_premises_ir d_idx) intro_rules

build_ir_args rec_args nonrec_args ir_name ir_type param_num = do
  num_params <- gets m_num_params
  param_const <- liftM (flip genericIndex param_num . m_param_consts) get
  case ir_type of
    Pi pi | param_num < num_params -> build_ir_args rec_args nonrec_args ir_name (instantiate (binding_body pi) (Local param_const)) (param_num+1)
          | otherwise -> do
      -- intro rule has an argument
      modify (\ind_data -> ind_data { m_K_target = False })
      local <- mk_local_for pi
      is_rec_arg <- is_rec_argument (binding_domain pi)
      if is_rec_arg
        then build_ir_args (rec_args ++ [local]) nonrec_args ir_name (instantiate (binding_body pi) (Local local)) (param_num+1)
        else build_ir_args rec_args (nonrec_args ++ [local]) ir_name (instantiate (binding_body pi) (Local local)) (param_num+1)
    _ -> return (rec_args,nonrec_args,ir_type)
    
populate_minor_premises_ir d_idx (IntroRule ir_name ir_type) = do
  (rec_args,nonrec_args,ir_type) <- build_ir_args [] [] ir_name ir_type 0
  (it_idx,it_indices) <- get_I_indices ir_type
  elim_infos <- gets m_elim_infos
  c_app <- return $ mk_app_seq (Local . m_C $ genericIndex elim_infos it_idx) it_indices
  dep_elim <- gets m_dep_elim
  levels <- gets m_levels
  param_consts <- gets m_param_consts
  c_app <- return $ if dep_elim then
                      let intro_app = mk_app_seq
                                      (mk_app_seq
                                       (mk_app_seq (mk_constant ir_name levels) (map Local param_consts))
                                       (map Local nonrec_args))
                                      (map Local rec_args) in
                      mk_app c_app intro_app
                    else c_app
  -- populate ind_args given rec_args
  -- we have one ind_arg for each rec_arg
  -- whenever we take an argument of the form (Pi other_type ind_type), we get to assume `C` holds for every possible output
  {- inductive blah := intro : bool -> (unit → blah) → blah
        blah.rec : Π {C : blah → Type},
          (Π (a : bool) (a_1 : unit → blah), (Π (a : unit), C (a_1 a)) → C (blah.intro a a_1)) → (Π (n : blah), C n) -}
  ind_args <- build_ind_args (zip rec_args [0..])
  fresh_name_minor <- mk_fresh_name      
  minor_ty <- return $ abstract_pi_seq nonrec_args
              (abstract_pi_seq rec_args
               (abstract_pi_seq ind_args c_app))
  minor_premise <- return $ mk_local_data fresh_name_minor (AppendInteger (mk_name ["e"]) d_idx) minor_ty
  push_minor_premise d_idx minor_premise

build_xs rec_arg_ty xs =
  case rec_arg_ty of
    Pi pi -> mk_local_for pi >>= (\x -> build_xs (instantiate (binding_body pi) (Local x)) (xs ++ [x]))
    _ -> return (xs,rec_arg_ty)

build_ind_args [] = return []
build_ind_args ((rec_arg,rec_arg_num):rest) = do
  rest_ind_args <- build_ind_args rest
  rec_arg_ty <- whnf (local_type rec_arg)
  (xs,rec_arg_ty) <- build_xs rec_arg_ty []
  (it_idx,it_indices) <- get_I_indices rec_arg_ty
  c <- liftM (m_C . (flip genericIndex it_idx) . m_elim_infos) get
  c_app <- return $ mk_app_seq (Local c) it_indices
  dep_elim <- gets m_dep_elim
  c_app <- return $ if dep_elim then mk_app c_app (mk_app_seq (Local rec_arg) (map Local xs)) else c_app
  ind_arg_ty <- return $ abstract_pi_seq xs c_app
  fresh_name_ind_arg <- mk_fresh_name
  ind_arg <- return $ mk_local_data fresh_name_ind_arg (AppendInteger (mk_name ["v"]) rec_arg_num) ind_arg_ty
  return $ ind_arg:rest_ind_args

{- Given t of the form (I As is) where I is one of the inductive datatypes being defined,
   As are the global parameters, and `is` the actual indices provided to it.
   Return the index of I, and store is in the argument \c indices. -}
get_I_indices rec_arg_ty = do
  maybe_it_idx <- get_valid_it_app_idx rec_arg_ty
  num_params <- gets m_num_params
  case maybe_it_idx of
    Just d_idx -> return (d_idx,genericDrop num_params (get_app_args rec_arg_ty))

-- TODO will need locals
declare_elim_rule (InductiveDecl name ty intro_rules) d_idx = do
  elim_info <- liftM (flip genericIndex d_idx . m_elim_infos) get
  c_app <- return $ mk_app_seq (Local $ m_C elim_info) (map Local $ m_indices elim_info)
  dep_elim <- gets m_dep_elim
  c_app <- return $ if dep_elim then mk_app c_app (Local $ m_major_premise elim_info) else c_app
  elim_type <- return $ abstract_pi (m_major_premise elim_info) c_app
  elim_type <- return $ abstract_pi_seq (m_indices elim_info) elim_type
  -- abstract all introduction rules
  elim_type <- abstract_all_introduction_rules elim_type
  elim_type <- abstract_all_type_formers elim_type
  param_consts <- gets m_param_consts
  elim_type <- return $ abstract_pi_seq param_consts elim_type
  level_names <- get_elim_level_param_names
  -- trace (show name ++ ".rec [" ++ show level_names ++ "]: " ++ show elim_type) (return ())
  cdecl <- certify_declaration (get_elim_name name) level_names elim_type
  -- trace "END_certify_declaration" (return ())
  update_m_env (flip env_add cdecl)

get_elim_name name = AppendString name "rec"
get_elim_name_idx it_idx = do
  idecls <- gets m_decls
  case genericIndex idecls it_idx of
    InductiveDecl name _ _ -> return $ get_elim_name name

abstract_all_introduction_rules elim_type = 
  gets m_elim_infos >>= return .
  (foldr (\(ElimInfo _ _ _ minor_premises) elim_type ->
          foldr (\minor_premise elim_type ->
                  abstract_pi minor_premise elim_type)
          elim_type
          minor_premises)
    elim_type)
  
abstract_all_type_formers elim_type =
  gets m_elim_infos >>= return . (foldr (\(ElimInfo c _ _ _) elim_type -> abstract_pi c elim_type) elim_type)

get_elim_level_params = do
  elim_level <- gets m_elim_level
  levels <- gets m_levels
  case elim_level of
    Just el@(LevelParam l) -> return $ el : levels
    _ -> return levels

get_elim_level_param_names = do
  elim_level <- gets m_elim_level
  level_names <- gets m_level_names
  case elim_level of
    Just (LevelParam l) -> return $ l : level_names
    _ -> return level_names

-- | Create computional rules RHS. They are used by the normalizer extension.
mk_comp_rules_rhs = do
  idecls <- gets m_decls
  elim_infos <- gets m_elim_infos
  mapM_ (uncurry mk_comp_rules_rhs_decl) (zip idecls elim_infos)

mk_comp_rules_rhs_decl (InductiveDecl name ty intro_rules) (ElimInfo _ indices _ minor_premises) = do
  ext_add_elim name (genericLength indices)
  mapM_ (uncurry $ register_comp_rhs name) (zip intro_rules minor_premises)

register_comp_rhs ind_name (IntroRule ir_name ir_type) minor_premise = do
  (rec_args,nonrec_args,ir_type) <- build_ir_args [] [] ir_name ir_type 0
  e_app <- build_e_app rec_args
  e_app <- return $ mk_app_seq (mk_app_seq (mk_app_seq (Local minor_premise) (map Local nonrec_args))
                                (map Local rec_args)) e_app
  param_consts <- gets m_param_consts
  cs <- liftM (map m_C . m_elim_infos) get
  minor_premises <- liftM (concat . map m_minor_premises . m_elim_infos) get
  comp_rhs <- return $
              abstract_lambda_seq param_consts
              (abstract_lambda_seq cs
               (abstract_lambda_seq minor_premises
                (abstract_lambda_seq nonrec_args
                 (abstract_lambda_seq rec_args e_app))))
  level_param_names <- get_elim_level_param_names
  check_type comp_rhs level_param_names
--  trace ("\ncomp_rhs: " ++ show comp_rhs ++ "\n") (return ())
  ext_add_comp_rhs ir_name (get_elim_name ind_name) (genericLength rec_args + genericLength nonrec_args) comp_rhs

build_e_app [] = return []
build_e_app (rec_arg:rest) = do
  rest_rhs <- build_e_app rest
  rec_arg_ty <- whnf (local_type rec_arg)
  (xs,rec_arg_ty) <- build_xs rec_arg_ty []
  (it_idx,it_indices) <- get_I_indices rec_arg_ty
  ls <- get_elim_level_params
  param_consts <- gets m_param_consts
  elim_infos <- gets m_elim_infos
  elim_name <- get_elim_name_idx it_idx
  elim_app <- return $ mk_constant elim_name ls
  elim_app <- return $ mk_app
              (mk_app_seq
               (mk_app_seq
                (mk_app_seq
                 (mk_app_seq elim_app (map Local param_consts))
                 (map (Local . m_C) elim_infos))
                (map Local . concat $ map m_minor_premises elim_infos))
               it_indices) -- TODO map Local?
              (mk_app_seq (Local rec_arg) (map Local xs))
  return $ (abstract_lambda_seq xs elim_app):rest_rhs

{- Wrappers for the type checker -}

check_type e level_names = do
  env <- gets m_env
  next_id <- gets m_next_id
  case TypeChecker.tc_eval env level_names next_id (TypeChecker.infer_type e) of
    Left tc_err -> throwE $ TypeCheckError tc_err "check_type"
    Right (e,next) -> modify (\tc -> tc { m_next_id = next }) >> return e

ensure_sort e = do
  env <- gets m_env
  level_names <- gets m_level_names
  next_id <- gets m_next_id
  case TypeChecker.tc_eval env level_names next_id (TypeChecker.ensure_sort e) of
    Left tc_err -> throwE $ TypeCheckError tc_err "ensure_sort"
    Right (sort,next) -> modify (\tc -> tc { m_next_id = next }) >> return sort

ensure_type e = do
  env <- gets m_env
  level_names <- gets m_level_names
  next_id <- gets m_next_id
  case TypeChecker.tc_eval env level_names next_id (TypeChecker.ensure_type e) of
    Left tc_err -> throwE $ TypeCheckError tc_err "ensure_type"
    Right (sort,next) -> modify (\tc -> tc { m_next_id = next }) >> return sort

is_def_eq e1 e2 = do
  env <- gets m_env
  level_names <- gets m_level_names
  next_id <- gets m_next_id
  case TypeChecker.tc_eval env level_names next_id (TypeChecker.is_def_eq e1 e2) of
    Left tc_err -> throwE $ TypeCheckError tc_err "is_def_eq"
    Right (b,next) -> modify (\tc -> tc { m_next_id = next }) >> return b

certify_ideclaration :: InductiveDecl -> AddInductiveMethod CertifiedDeclaration
certify_ideclaration (InductiveDecl name ty intro_rules) = do
  level_names <- gets m_level_names
  certify_declaration name level_names ty

certify_declaration :: Name -> [Name] -> Expression -> AddInductiveMethod CertifiedDeclaration
certify_declaration name level_names ty = do
  env <- gets m_env
  next_id <- gets m_next_id
  let decl = mk_axiom name level_names ty in
    case TypeChecker.tc_eval env level_names next_id (TypeChecker.check_main decl) of
      Left tc_err -> throwE $ TypeCheckError tc_err "certify_declaration"
      Right (cdecl,next) -> modify (\tc -> tc { m_next_id = next }) >> return cdecl

whnf e = do
  env <- gets m_env
  level_names <- gets m_level_names
  next_id <- gets m_next_id
  case TypeChecker.tc_eval env level_names next_id (TypeChecker.whnf e) of
    Left tc_err -> throwE $ TypeCheckError tc_err "whnf"
    Right (e,next) -> modify (\tc -> tc { m_next_id = next }) >> return e


-- TODO whnf that takes env and level names as arguments


-- Other helpers
replaceAtIndex ls n item = a ++ (item:b) where (a, (_:b)) = genericSplitAt n ls

push_minor_premise d_idx minor_premise = do
  elim_infos <- gets m_elim_infos
  let old_elim_info = genericIndex elim_infos d_idx
      old_minor_premises = m_minor_premises old_elim_info
      new_elim_info = old_elim_info { m_minor_premises = old_minor_premises ++ [minor_premise] }
    in
   modify (\ind_data -> ind_data { m_elim_infos = replaceAtIndex elim_infos d_idx new_elim_info })

update_m_env f = do
  env <- gets m_env
  modify (\ind_data -> ind_data { m_env = f env })
           
{- Extensions -}

ext_add_inductive_info = do
  ind_data <- get
  update_m_env (ind_ext_add_inductive_info (m_level_names ind_data)
                (m_num_params ind_data)
                (m_decls ind_data))

ext_add_intro_info ir_name ind_name = update_m_env $ ind_ext_add_intro_info ir_name ind_name 

ext_add_elim ind_name num_indices = do
  elim_level_param_names <- get_elim_level_param_names
  ind_data <- get
  num_cs <- liftM (genericLength . m_decls) get
  num_minor_ps <- return $ sum $ map (genericLength . m_minor_premises) $ m_elim_infos ind_data
  update_m_env (ind_ext_add_elim
                (get_elim_name ind_name)
                ind_name
                elim_level_param_names
                (m_num_params ind_data)
                (m_num_params ind_data + num_cs + num_minor_ps)
                (num_indices)
                (m_K_target ind_data)
                (m_dep_elim ind_data))


ext_add_comp_rhs ir_name elim_name num_rec_args_nonrec_args comp_rhs =
  update_m_env (ind_ext_add_comp_rhs ir_name elim_name num_rec_args_nonrec_args comp_rhs)

