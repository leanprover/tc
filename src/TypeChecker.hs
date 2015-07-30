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

module TypeChecker where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Except
import Data.List (nub,find,genericIndex,genericLength,genericTake,genericDrop,genericSplitAt)

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Maybe as Maybe

import Debug.Trace

import Util
import Name
import Level
import Expression
import Environment

data TypeError = UndefGlobalUniv Name
               | UndefUnivParam Name
               | TypeExpected Expression
               | FunctionExpected Expression                 
               | TypeMismatchAtApp Expression Expression
               | TypeMismatchAtDef Expression Expression
               | DefHasFreeVars Expression
               | DefHasLocals Expression
               | NameAlreadyDeclared Declaration
               | DuplicateParam
               | ConstNotFound ConstantData
               | WrongNumUnivParams Name [Name] [Level]
               | KernelError
               | NYI
                 deriving (Eq,Show)

data TypeChecker = TypeChecker { tc_env :: Environment , tc_level_names :: [Name] }
type Gensym = StateT Integer
type TCMethod = Gensym (ReaderT TypeChecker (Either TypeError))

check :: Environment -> Declaration -> Either TypeError CertifiedDeclaration
check env d = tc_run env (decl_level_names d) 0 (check_main d)

tc_run :: Environment -> [Name] -> Integer -> TCMethod a -> Either TypeError a
tc_run env level_names next_id tcm = flip runReaderT (TypeChecker env level_names) $ evalStateT tcm next_id

check_main :: Declaration -> TCMethod CertifiedDeclaration
check_main d = do
  tc <- ask
  check_no_local (decl_type d)
  maybe (return ()) check_no_local (decl_mb_val d)
  check_name (decl_name d)
  check_duplicated_params
  -- trace "about to check type" (return ())
  sort <- infer_type (decl_type d)
  -- trace "about to ensure sort" (return ())  
  ensure_sort sort
  -- trace "about to check val" (return ())
  maybe (return ()) (check_val_matches_ty (decl_type d)) (decl_mb_val d)
  -- trace "done" (return ())  
  return $ mk_certified_declaration (tc_env tc) d

------

--run_TCMethod tcm = evalStateT tcm
  
tc_fail = lift . lift . Left

tc_assert b err = if b then return () else tc_fail err

check_no_local e = tc_assert (not $ has_local e) (DefHasLocals e)
check_name name = ask >>= (\tc -> maybe (return ()) (tc_fail . NameAlreadyDeclared) (lookup_declaration (tc_env tc) name))
check_duplicated_params = ask >>= (\tc -> tc_assert (tc_level_names tc == nub (tc_level_names tc)) DuplicateParam)
check_val_matches_ty ty val = do
  val_ty <- infer_type val
  is_eq <- is_def_eq val_ty ty
  tc_assert is_eq (TypeMismatchAtDef val_ty ty)

ensure_sort :: Expression -> TCMethod SortData
ensure_sort e = case e of
  Sort sort -> return sort
  _ -> do
    e_whnf <- whnf e
    case e_whnf of
      Sort sort -> return sort
      _ -> tc_fail $ TypeExpected e_whnf

ensure_type :: Expression -> TCMethod SortData
ensure_type e = infer_type e >>= ensure_sort

ensure_pi :: Expression -> TCMethod BindingData
ensure_pi e = case e of
  Pi pi -> return pi
  _ -> do
    e_whnf <- whnf e
    case e_whnf of
      Pi pi -> return pi
      _ -> tc_fail $ FunctionExpected e_whnf

------

infer_type :: Expression -> TCMethod Expression
infer_type e = do
--  trace ("infer_type: " ++ show e ++ "\n") return ()
  check_closed e
  case e of
    Local local -> return $ local_type local
    Sort sort -> let level = sort_level sort in check_level level >> return (mk_sort (mk_succ level))
    Constant constant -> infer_constant constant
    Lambda lambda -> infer_lambda lambda
    Pi pi -> infer_pi pi
    App app -> infer_app app

check_closed e = tc_assert (not $ has_free_vars e) (DefHasFreeVars e)

check_level level = do
  tc <- ask
  maybe (return ()) (tc_fail . UndefGlobalUniv) (get_undef_global level (env_global_names $ tc_env tc))
  maybe (return ()) (tc_fail . UndefUnivParam)  (get_undef_param level (tc_level_names tc))

infer_constant :: ConstantData -> TCMethod Expression
infer_constant c = do
  tc <- ask
  case lookup_declaration (tc_env tc) (const_name c) of
    Nothing -> tc_fail (ConstNotFound c)
    Just d -> do
      (d_level_names,c_levels) <- return $ (decl_level_names d, const_levels c)
      tc_assert (length d_level_names == length c_levels) $ WrongNumUnivParams (const_name c) d_level_names c_levels
      mapM_ (\level -> check_level level) c_levels
      const_type <- return $ instantiate_univ_params (decl_type d) d_level_names c_levels
      return const_type

mk_local_for :: BindingData -> TCMethod LocalData
mk_local_for bind = do
  next_id <- gensym
  return $ mk_local_data_full (mk_system_name next_id) (binding_name bind) (binding_domain bind) (binding_info bind)
  
infer_lambda :: BindingData -> TCMethod Expression
infer_lambda lam = do
  domain_ty <- infer_type (binding_domain lam)
  ensure_sort domain_ty
  local <- mk_local_for lam
  body_ty <- infer_type (instantiate (binding_body lam) (Local local))
  return $ abstract_pi local body_ty

infer_pi :: BindingData -> TCMethod Expression
infer_pi pi = do
  domain_ty <- infer_type (binding_domain pi)
  domain_ty_as_sort <- ensure_sort domain_ty
  local <- mk_local_for pi
  body_ty <- infer_type (instantiate (binding_body pi) (Local local))
  body_ty_as_sort <- ensure_sort body_ty
  return $ mk_sort (mk_imax (sort_level domain_ty_as_sort) (sort_level body_ty_as_sort))

infer_app :: AppData -> TCMethod Expression
infer_app app = do
  op_ty <- infer_type (app_fn app)
  op_ty_as_pi <- ensure_pi op_ty
  arg_ty <- infer_type (app_arg app)
  is_eq <- is_def_eq (binding_domain op_ty_as_pi) arg_ty
  if is_eq then return $ instantiate (binding_body op_ty_as_pi) (app_arg app)
    else tc_fail $ TypeMismatchAtApp (binding_domain op_ty_as_pi) arg_ty


-- Weak-head normal form (whnf)

-- Interface

whnf :: Expression -> TCMethod Expression
whnf e = do
  -- trace ("whnf (" ++ show e ++ ")\n") (return ())
  e1 <- whnf_core_delta 0 e
  mb_e2 <- normalize_ext e1
  case mb_e2 of
    Nothing -> return e1
    Just e2 -> whnf e2

whnf_core_delta :: Integer -> Expression -> TCMethod Expression
whnf_core_delta w e = do
  e1 <- whnf_core e
  e2 <- unfold_names w e1
  if e == e2 then return e else whnf_core_delta w e2

whnf_core :: Expression -> TCMethod Expression
whnf_core e = case e of
  App app -> do
    (fn,arg) <- return $ app_fn_arg app
    fn_whnf <- whnf_core fn
    case fn_whnf of
      Lambda lam -> whnf_core (instantiate (binding_body lam) arg)
      otherwise -> if fn_whnf == fn then return e else whnf_core (mk_app fn_whnf arg)
  _ -> return e

unfold_names :: Integer -> Expression -> TCMethod Expression
unfold_names w e = case e of
  App app -> let op = get_operator e
                 args = get_app_args e
             in unfold_name_core w op >>= return . flip mk_app_seq args
  _ -> unfold_name_core w e

-- Why am I not finding ".not"?
unfold_name_core :: Integer -> Expression -> TCMethod Expression
unfold_name_core w e = case e of
  Constant const -> do
    -- trace ("unfold_name_core (" ++ (show const) ++ ")\n") (return ())
    tc <- ask
    maybe (trace "NOT FOUND" $ return e) -- DEL-CAREFUL
      (\d -> case decl_mb_val d of
          Just decl_val
            | decl_weight d >= w && length (const_levels const) == length (decl_level_names d)
              -> unfold_name_core w (instantiate_univ_params decl_val (decl_level_names d) $ const_levels const)
          _ -> do
            -- trace ("NO VALUE: {name= " ++ show (decl_name d) ++ " , weight= " ++ show (decl_weight d) ++ "(" ++ show w ++ ") }\n") (return ())
            return e)
      (lookup_declaration (tc_env tc) (const_name const))
  _ -> return e

-- TODO QUOTIENT iterate over all normalizer extensions
normalize_ext :: Expression -> TCMethod (Maybe Expression)
normalize_ext e = do
  env <- asks tc_env
  return $ inductive_norm_ext env e
                            

-- is_def_eq

is_def_eq :: Expression -> Expression -> TCMethod Bool
is_def_eq t s = do
--  trace ("<is_def_eq>\n\n" ++ show t ++ "\n\n" ++ show s ++ "\n\n\n") (return ())
  success <- runExceptT (is_def_eq_main t s)
  case success of
    Left answer -> return answer
    Right () -> return False

-- | If 'def_eq' short-circuits, then 'deq_commit_to def_eq' short-circuits with the same value, otherwise it shortcircuits with False.
deq_commit_to :: DefEqMethod () -> DefEqMethod ()
deq_commit_to def_eq = def_eq >> throwE False

-- | 'deq_try_and' proceeds through its arguments, and short-circuits with True if all arguments short-circuit with True, otherwise it does nothing.
deq_try_and :: [DefEqMethod ()] -> DefEqMethod ()
deq_try_and [] = throwE True
deq_try_and (def_eq:def_eqs) = do
  success <- lift $ runExceptT def_eq
  case success of
    Left True -> deq_try_and def_eqs
    _ -> return ()

-- | 'deq_try_or' proceeds through its arguments, and short-circuits with True if any of its arguments short-circuit with True, otherwise it does nothing.
deq_try_or :: [DefEqMethod ()] -> DefEqMethod ()
deq_try_or [] = return ()
deq_try_or (def_eq:def_eqs) = do
  success <- lift $ runExceptT def_eq
  case success of
    Left True -> throwE True
    _ -> deq_try_or def_eqs

{-
deq_true_as_continue :: DefEqMethod () -> DefEqMethod ()
deq_true_as_continue def_eq = do
  success <- lift $ runExceptT def_eq
  case success of
    Left True -> return ()
    _ -> throwE False
-}

-- This exception means we know if they are equal or not
type DefEqMethod = ExceptT Bool TCMethod

-- deq_fail = lift . tc_fail
deq_assert b err = lift $ tc_assert b err

-- | 'try_if b check' tries 'check' only if 'b' is true, otherwise does nothing.
try_if :: Bool -> DefEqMethod () -> DefEqMethod ()
try_if b check = if b then check else return ()


is_def_eq_main :: Expression -> Expression -> DefEqMethod ()
is_def_eq_main t s = do
  quick_is_def_eq t s
  t_n <- lift $ whnf_core t
  s_n <- lift $ whnf_core s
  try_if (t_n /= t || s_n /= s) (quick_is_def_eq t_n s_n)
  (t_n,s_n) <- reduce_def_eq t_n s_n

  case (t_n,s_n) of
    (Constant const1, Constant const2) | const_name const1 == const_name const2 &&
                                         is_def_eq_levels (const_levels const1) (const_levels const2) -> throwE True
    (Local local1, Local local2) | local_name local1 == local_name local2 ->
      throwE True
    (App app1,App app2) -> deq_commit_to (is_def_eq_app t_n s_n)
    _ -> return ()

  is_eq_eta_expansion t_n s_n
  is_def_proof_irrel t_n s_n

reduce_def_eq :: Expression -> Expression -> DefEqMethod (Expression,Expression)
reduce_def_eq t s = do
  (t,s,status) <- lazy_delta_reduction t s >>= uncurry ext_reduction_step
  case status of
    DefUnknown -> return (t,s)
    Continue -> reduce_def_eq t s

ext_reduction_step :: Expression -> Expression -> DefEqMethod (Expression,Expression,ReductionStatus)
ext_reduction_step t_n s_n = do
  new_t_n <- lift $ normalize_ext t_n
  new_s_n <- lift $ normalize_ext s_n

  (t,s,status) <- case (new_t_n,new_s_n) of
    (Nothing,Nothing) -> return (t_n,s_n,DefUnknown)
    (Just t_n,Nothing) -> do t_nn <- lift $ whnf_core t_n
                             return (t_nn,s_n,Continue)
    (Nothing,Just s_n) -> do s_nn <- lift $ whnf_core s_n
                             return (t_n,s_nn,Continue)
    (Just t_n,Just s_n) -> do t_nn <- lift $ whnf_core t_n
                              s_nn <- lift $ whnf_core s_n                              
                              return (t_nn,s_nn,Continue)

  case status of
    DefUnknown -> return (t,s,DefUnknown)
    Continue -> quick_is_def_eq t s >> return (t,s,Continue)

lazy_delta_reduction :: Expression -> Expression -> DefEqMethod (Expression,Expression)
lazy_delta_reduction t s = do
  (t_n,s_n,status) <- lazy_delta_reduction_step t s
  case status of
    DefUnknown -> return (t_n,s_n)    
    Continue -> lazy_delta_reduction t_n s_n

data ReductionStatus = Continue | DefUnknown
append_to_pair (x,y) z = (x,y,z)

is_delta :: Environment -> Expression -> Maybe Declaration
is_delta env e = case (get_operator e) of
  Constant const -> case lookup_declaration env (const_name const) of
    Just d | is_definition d -> Just d
    _ -> Nothing
  _ -> Nothing

-- | Perform one lazy delta-reduction step.
lazy_delta_reduction_step :: Expression -> Expression -> DefEqMethod (Expression,Expression,ReductionStatus)
lazy_delta_reduction_step t s = do
  tc <- ask
  (md_t,md_s) <- return $ (is_delta (tc_env tc) t,is_delta (tc_env tc) s)
  (t_n,s_n,status) <-
    case (md_t,md_s) of
      (Nothing,Nothing) -> return (t,s,DefUnknown)
      (Just d_t,Nothing) -> do t_dn <- lift (unfold_names 0 t >>= whnf_core)
                               return (t_dn,s,Continue)
      (Nothing,Just d_s) -> do s_dn <- lift (unfold_names 0 s >>= whnf_core)
                               return (t,s_dn,Continue)
      (Just d_t,Just d_s) -> lazy_delta_reduction_step_helper d_t d_s t s >>= return . (flip append_to_pair Continue)

  case status of
    DefUnknown -> return (t_n,s_n,DefUnknown)
    Continue -> quick_is_def_eq t_n s_n >> return (t_n,s_n,Continue)

lazy_delta_reduction_step_helper :: Declaration -> Declaration -> Expression -> Expression -> DefEqMethod (Expression,Expression)
lazy_delta_reduction_step_helper d_t d_s t s = do
  tc <- ask
  case compare (decl_weight d_t) (decl_weight d_s) of
    LT -> do s_dn <- lift (unfold_names (decl_weight d_t + 1) s >>= whnf_core)
             return (t,s_dn)
    GT -> do t_dn <- lift (unfold_names (decl_weight d_s + 1) t >>= whnf_core)
             return (t_dn,s)
    EQ ->
      case (t,s) of
        (App t_app, App s_app) -> do
          {- Optimization: we try to check if their arguments are definitionally equal.
             If they are, then t_n and s_n must be definitionally equal,
             and we can skip the delta-reduction step. -}
          is_def_eq_app t s
          reduce_both
        _ -> reduce_both
      where
        reduce_both = do
          t_dn <- lift (unfold_names (decl_weight d_s - 1) t >>= whnf_core)
          s_dn <- lift (unfold_names (decl_weight d_t - 1) s >>= whnf_core)
          return (t_dn,s_dn)

{- | Throw true if 't' and 's' are definitionally equal because they are applications of the form
    '(f a_1 ... a_n)' and '(g b_1 ... b_n)', where 'f' and 'g' are definitionally equal, and
    'a_i' and 'b_i' are also definitionally equal for every 1 <= i <= n.
    Throw 'False' otherwise.
-}
is_def_eq_app :: Expression -> Expression -> DefEqMethod ()
is_def_eq_app t s =
  deq_try_and [is_def_eq_main (get_operator t) (get_operator s),
               throwE (genericLength (get_app_args t) == genericLength (get_app_args s)),
               mapM_ (uncurry is_def_eq_main) (zip (get_app_args t) (get_app_args s))]
  
is_eq_eta_expansion :: Expression -> Expression -> DefEqMethod ()
is_eq_eta_expansion t s = deq_try_or [is_eq_by_eta_expansion_core t s, is_eq_by_eta_expansion_core s t]

-- | Try to solve (fun (x : A), B) =?= s by trying eta-expansion on s
-- The 'by' indicates that it short-circuits False 't' and 's' are not equal by eta-expansion, even though they may be equal for another reason. The enclosing 'deq_any_of' ignores any 'False's.
is_eq_by_eta_expansion_core :: Expression -> Expression -> DefEqMethod ()
is_eq_by_eta_expansion_core t s = go t s where
  go (Lambda lam1) (Lambda lam2) = throwE False
  go (Lambda lam1) s = do
    s_ty_n <- lift $ infer_type s >>= whnf
    case s_ty_n of
      Pi pi -> let new_s = mk_lambda (binding_name pi) (binding_domain pi) (mk_app s (mk_var 0)) (binding_info pi) in do
        deq_commit_to (is_def_eq_main t new_s)
      _ -> throwE False
  go _ _ = throwE False
  
is_prop :: Expression -> TCMethod Bool
is_prop e = do
  e_ty <- infer_type e
  e_ty_whnf <- whnf e_ty
  return $ if e_ty_whnf == mk_Prop then True else False

-- TODO query environment to see if proof irrelevance is enabled
is_def_proof_irrel :: Expression -> Expression -> DefEqMethod ()
is_def_proof_irrel t s = do
  t_ty <- lift $ infer_type t
  s_ty <- lift $ infer_type s
  t_ty_is_prop <- lift $ is_prop t_ty
  try_if t_ty_is_prop (is_def_eq_main t_ty s_ty)

quick_is_def_eq :: Expression -> Expression -> DefEqMethod ()
quick_is_def_eq t s = case (t,s) of
  (Lambda lam1, Lambda lam2) -> deq_commit_to (is_def_eq_binding lam1 lam2)
  (Pi pi1, Pi pi2) -> deq_commit_to (is_def_eq_binding pi1 pi2)
  (Sort sort1, Sort sort2) -> throwE (level_equiv (sort_level sort1) (sort_level sort2))
  _ -> return ()

-- | Given lambda/Pi expressions 't' and 's', return true iff 't' is def eq to 's', which holds iff 'domain(t)' is definitionally equal to 'domain(s)' and 'body(t)' is definitionally equal to 'body(s)'
is_def_eq_binding :: BindingData -> BindingData -> DefEqMethod ()
is_def_eq_binding bind1 bind2 = do
  deq_try_and  [(is_def_eq_main (binding_domain bind1) (binding_domain bind2)),
                do next_id <- lift gensym
                   local <- return $ mk_local (mk_system_name next_id) (binding_name bind1) (binding_domain bind1) (binding_info bind1)
                   is_def_eq_main (instantiate (binding_body bind1) local) (instantiate (binding_body bind2) local)]


is_def_eq_levels :: [Level] -> [Level] -> Bool
is_def_eq_levels ls1 ls2 = all (True==) (map (uncurry level_equiv) (zip ls1 ls2))
               


-----
gensym :: StateT Integer (ReaderT TypeChecker (Either TypeError)) Integer
gensym = do
  n <- get
  put (n+1)
  return n

-- TODO make sure only this module can create these
mk_certified_declaration env d = CertifiedDeclaration env d


{- extensions -}

-- | Reduce terms 'e' of the form 'elim_k A C e p[A,b] (intro_k_i A b u)'
inductive_norm_ext :: Environment -> Expression -> Maybe Expression
-- TODO this may throw an error (though I don't think it is possible for it to do so)
inductive_norm_ext env e = do
  elim_fn_const <- maybe_constant (get_operator e)
  einfo@(ExtElimInfo ind_name lp_names num_params num_ACe num_indices k_target dep_elim) <-
    Map.lookup (const_name elim_fn_const) (iext_elim_infos $ env_ind_ext env)
  guard $ genericLength (get_app_args e) >= num_ACe + num_indices + 1
  let major_idx = num_ACe + num_indices
      major = genericIndex (get_app_args e) major_idx in do
    (intro_app,comp_rule) <- find_comp_rule env einfo elim_fn_const lp_names major
    let elim_args = get_app_args e
        intro_args = get_app_args intro_app in do
      guard $ genericLength intro_args == num_params + (cr_num_rec_nonrec_args comp_rule)
      guard $ genericLength (const_levels elim_fn_const) == genericLength lp_names
      let rhs_args = reverse ((genericTake num_ACe elim_args) ++
                              (genericTake (cr_num_rec_nonrec_args comp_rule) $ genericDrop num_params intro_args))
          rhs_body = instantiate_univ_params (body_of_lambda $ cr_comp_rhs comp_rule) lp_names (const_levels elim_fn_const)
          rhs_body_instantiated = instantiate_seq rhs_body rhs_args
          extra_args = genericDrop (major_idx + 1) elim_args in do
        return $ mk_app_seq rhs_body_instantiated extra_args
  where
    find_comp_rule env einfo elim_fn_const lp_names major
      | eei_K_target einfo =
        maybe (regular_comp_rule env einfo elim_fn_const lp_names major) Just
        (do intro_app <- to_intro_when_K env einfo lp_names major
            intro_app_op_const <- maybe_constant (get_operator intro_app)
            comp_rule <- Map.lookup (const_name intro_app_op_const) (iext_comp_rules (env_ind_ext env))
            return (intro_app,comp_rule))
      | otherwise = regular_comp_rule env einfo elim_fn_const lp_names major
    regular_comp_rule env einfo elim_fn_const lp_names major = do
      intro_app <- return . skip_exceptions $ tc_run env lp_names 0 (whnf major)
      comp_rule <- is_intro_for env (const_name elim_fn_const) intro_app
      return (intro_app,comp_rule)
    


-- | Return 'True' if 'e' is an introduction rule for an eliminator named 'elim'
is_intro_for :: Environment -> Name -> Expression -> Maybe CompRule
is_intro_for env elim_name e = do
  intro_fn_const <- maybe_constant (get_operator e)
  comp_rule <- Map.lookup (const_name intro_fn_const) (iext_comp_rules $ env_ind_ext env)
  guard (cr_elim_name comp_rule == elim_name)
  return comp_rule

skip_exceptions tc = case tc of
  Left _ -> error "type checker should not throw error inside inductive_norm_ext"
  Right e -> e
  
-- | For datatypes that support K-axiom, given e an element of that type, we convert (if possible)
-- to the default constructor. For example, if (e : a = a), then this method returns (eq.refl a)
to_intro_when_K :: Environment -> ExtElimInfo -> [Name] -> Expression -> Maybe Expression
to_intro_when_K env einfo lp_names e = do
  return $ assert (eei_K_target einfo) "to_intro_when_K should only be called when K_target holds"
  app_type <- return . skip_exceptions $ tc_run env lp_names 0 (infer_type e >>= whnf)
  app_type_I <- return $ get_operator app_type
  app_type_I_const <- maybe_constant app_type_I
  guard (const_name app_type_I_const == eei_inductive_name einfo)
  new_intro_app <- mk_nullary_intro env app_type (eei_num_params einfo)
  new_type <- return . skip_exceptions $ tc_run env lp_names 0 (infer_type new_intro_app)
  guard (skip_exceptions $ tc_run env lp_names 0 (is_def_eq app_type new_type))
  return new_intro_app

-- | If 'op_name' is the name of a non-empty inductive datatype, then return the
--   name of the first introduction rule. Return 'Nothing' otherwise.
get_first_intro env op_name = do
  mutual_idecls <- Map.lookup op_name (iext_ind_infos $ env_ind_ext env)
  InductiveDecl _ _ intro_rules <- find (\(InductiveDecl ind_name _ _) -> ind_name == op_name) (mid_idecls mutual_idecls)
  IntroRule ir_name _ <- find (\_ -> True) intro_rules
  return ir_name

  
mk_nullary_intro env app_type num_params = 
  let (op,args) = get_app_op_args app_type in do
    op_const <- maybe_constant op
    intro_name <- get_first_intro env (const_name op_const)
    return $ mk_app_seq (mk_constant intro_name (const_levels op_const)) (genericTake num_params args)
