{-|
Module      : TypeChecker
Description : Type checker
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

The TypeChecker modules includes the core type-checker, whnf, is_def_eq, and both normalizer extensions.
-}
module TypeChecker (TypeChecker (..),
                    TypeError (..),
                    TCMethod,
                    tc_eval,tc_run,
                    check,check_main,
                    infer_type,whnf,is_def_eq,ensure_type,ensure_sort
                   )
where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
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
import qualified EquivManager as EM

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

data TypeChecker = TypeChecker {
  tc_env :: Environment ,
  tc_level_names :: [Name] ,
  tc_next_id :: Integer ,
  tc_equiv_manager :: EM.EquivManager,
  tc_infer_type_cache :: Map Expression Expression
  }

mk_type_checker env level_names next_id = TypeChecker env level_names next_id EM.empty_equiv_manager Map.empty

type TCMethod = ExceptT TypeError (State TypeChecker)

check :: Environment -> Declaration -> Either TypeError CertifiedDeclaration
check env d = fmap fst $ tc_eval env (decl_level_names d) 0 (check_main d)

tc_eval :: Environment -> [Name] -> Integer -> TCMethod a -> Either TypeError (a,Integer)
tc_eval env level_names next_id tc_fn =
  let (x,tc) = runState (runExceptT tc_fn) (mk_type_checker env level_names next_id) in
  fmap (\val -> (val,tc_next_id tc)) x

tc_run :: Environment -> [Name] -> Integer -> TCMethod a -> Either TypeError a
tc_run env level_names next_id tc_fn = evalState (runExceptT tc_fn) (mk_type_checker env level_names next_id)


check_main :: Declaration -> TCMethod CertifiedDeclaration
check_main d = do
  tc <- get
  check_no_local (decl_type d)
  maybe (return ()) check_no_local (decl_mb_val d)
  check_name (decl_name d)
  check_duplicated_params
  sort <- infer_type (decl_type d)
  ensure_sort sort
  maybe (return ()) (check_val_matches_ty (decl_type d)) (decl_mb_val d)
  return $ mk_certified_declaration (tc_env tc) d

------

tc_assert b err = if b then return () else throwE err

check_no_local e = tc_assert (not $ has_local e) (DefHasLocals e)
check_name name = get >>= (\tc -> maybe (return ()) (throwE . NameAlreadyDeclared) (lookup_declaration (tc_env tc) name))
check_duplicated_params = get >>= (\tc -> tc_assert (tc_level_names tc == nub (tc_level_names tc)) DuplicateParam)
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
      _ -> throwE $ TypeExpected e_whnf

ensure_type :: Expression -> TCMethod SortData
ensure_type e = infer_type e >>= ensure_sort

ensure_pi :: Expression -> TCMethod BindingData
ensure_pi e = case e of
  Pi pi -> return pi
  _ -> do
    e_whnf <- whnf e
    case e_whnf of
      Pi pi -> return pi
      _ -> throwE $ FunctionExpected e_whnf

------

infer_type :: Expression -> TCMethod Expression
infer_type e = do
  check_closed e
  infer_type_cache <- gets tc_infer_type_cache
  case Map.lookup e infer_type_cache of
    Just t -> return t
    Nothing -> do 
      t <- case e of
        Local local -> return $ local_type local
        Sort sort -> let level = sort_level sort in check_level level >> return (mk_sort (mk_succ level))
        Constant constant -> infer_constant constant
        Lambda lambda -> infer_lambda lambda
        Pi pi -> infer_pi pi
        App app -> infer_app app
      infer_type_cache <- gets tc_infer_type_cache
      modify (\tc -> tc { tc_infer_type_cache = Map.insert e t infer_type_cache })
      return t

check_closed e = tc_assert (not $ has_free_vars e) (DefHasFreeVars e)

check_level level = do
  tc <- get
  maybe (return ()) (throwE . UndefGlobalUniv) (get_undef_global level (env_global_names $ tc_env tc))
  maybe (return ()) (throwE . UndefUnivParam)  (get_undef_param level (tc_level_names tc))

infer_constant :: ConstantData -> TCMethod Expression
infer_constant c = do
  tc <- get
  case lookup_declaration (tc_env tc) (const_name c) of
    Nothing -> throwE (ConstNotFound c)
    Just d -> do
      (d_level_names,c_levels) <- return $ (decl_level_names d, const_levels c)
      tc_assert (length d_level_names == length c_levels) $ WrongNumUnivParams (const_name c) d_level_names c_levels
      mapM_ (\level -> check_level level) c_levels
      const_type <- return $ instantiate_univ_params (decl_type d) d_level_names c_levels
      return const_type

mk_local_for :: BindingData -> TCMethod LocalData
mk_local_for bind = do
  next_id <- gensym
  return $ mk_local_data_full (mk_system_name_i next_id) (binding_name bind) (binding_domain bind) (binding_info bind)
  
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
    else throwE $ TypeMismatchAtApp (binding_domain op_ty_as_pi) arg_ty


-- Weak-head normal form (whnf)

-- Interface

whnf :: Expression -> TCMethod Expression
whnf e = do
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
    (fn,arg) <- return $ (app_fn app, app_arg app)
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

unfold_name_core :: Integer -> Expression -> TCMethod Expression
unfold_name_core w e = case e of
  Constant const -> do
    tc <- get
    maybe (return e)
      (\d -> case decl_mb_val d of
          Just decl_val
            | decl_weight d >= w && length (const_levels const) == length (decl_level_names d)
              -> unfold_name_core w (instantiate_univ_params decl_val (decl_level_names d) $ const_levels const)
          _ -> return e)
      (lookup_declaration (tc_env tc) (const_name const))
  _ -> return e

normalize_ext :: Expression -> TCMethod (Maybe Expression)
normalize_ext e = runMaybeT (inductive_norm_ext e `mplus` quotient_norm_ext e)

-- is_def_eq

is_def_eq :: Expression -> Expression -> TCMethod Bool
is_def_eq t s = do
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

-- This exception means we know if they are equal or not
type DefEqMethod = ExceptT Bool TCMethod

deq_assert b err = lift $ tc_assert b err

-- | 'deq_try_if b check' tries 'check' only if 'b' is true, otherwise does nothing.
deq_try_if :: Bool -> DefEqMethod () -> DefEqMethod ()
deq_try_if b check = if b then check else return ()

-- | Wrapper to add successes to the cache
is_def_eq_main :: Expression -> Expression -> DefEqMethod ()
is_def_eq_main t s = do
  success <- lift $ runExceptT (is_def_eq_core t s)
  case success of
    Left True -> em_add_equiv t s >> throwE True
    Left False -> throwE False
    Right () -> return ()

is_def_eq_core :: Expression -> Expression -> DefEqMethod ()
is_def_eq_core t s = do
  quick_is_def_eq t s
  t_n <- lift $ whnf_core t
  s_n <- lift $ whnf_core s
  deq_try_if (t_n /= t || s_n /= s) $ quick_is_def_eq t_n s_n
  (t_n,s_n) <- reduce_def_eq t_n s_n

  case (t_n,s_n) of
    (Constant const1, Constant const2) | const_name const1 == const_name const2 &&
                                         is_def_eq_levels (const_levels const1) (const_levels const2) -> throwE True
    (Local local1, Local local2) | local_name local1 == local_name local2 ->
      throwE True
    (App app1,App app2) -> deq_commit_to (is_def_eq_app t_n s_n)
    _ -> return ()

  is_eq_eta_expansion t_n s_n
  gets tc_env >>= (\env -> deq_try_if (is_prop_proof_irrel env) $ is_def_proof_irrel t_n s_n)
  

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
  tc <- get
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
  tc <- get
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

is_def_proof_irrel :: Expression -> Expression -> DefEqMethod ()
is_def_proof_irrel t s = do
  t_ty <- lift $ infer_type t
  s_ty <- lift $ infer_type s
  t_ty_is_prop <- lift $ is_prop t_ty
  deq_try_if t_ty_is_prop $ is_def_eq_main t_ty s_ty

quick_is_def_eq :: Expression -> Expression -> DefEqMethod ()
quick_is_def_eq t s = do
  em_is_equiv t s
  case (t,s) of
    (Lambda lam1, Lambda lam2) -> deq_commit_to (is_def_eq_binding lam1 lam2)
    (Pi pi1, Pi pi2) -> deq_commit_to (is_def_eq_binding pi1 pi2)
    (Sort sort1, Sort sort2) -> throwE (level_equiv (sort_level sort1) (sort_level sort2))
    _ -> return ()

-- | Given lambda/Pi expressions 't' and 's', return true iff 't' is def eq to 's', which holds iff 'domain(t)' is definitionally equal to 'domain(s)' and 'body(t)' is definitionally equal to 'body(s)'
is_def_eq_binding :: BindingData -> BindingData -> DefEqMethod ()
is_def_eq_binding bind1 bind2 = do
  deq_try_and  [(is_def_eq_main (binding_domain bind1) (binding_domain bind2)),
                do next_id <- lift gensym
                   local <- return $ mk_local (mk_system_name_i next_id) (binding_name bind1) (binding_domain bind1) (binding_info bind1)
                   is_def_eq_main (instantiate (binding_body bind1) local) (instantiate (binding_body bind2) local)]


is_def_eq_levels :: [Level] -> [Level] -> Bool
is_def_eq_levels ls1 ls2 = genericLength ls1 == genericLength ls2 &&
                           all (True==) (map (uncurry level_equiv) (zip ls1 ls2))

-----
gensym :: TCMethod Integer
gensym = do
  n <- gets tc_next_id
  modify (\tc -> tc { tc_next_id = n+1 })
  return n

-- TODO make sure only this module can create these
mk_certified_declaration env d = CertifiedDeclaration env d

{- caching for is_def_eq -}

em_add_equiv :: Expression -> Expression -> DefEqMethod ()
em_add_equiv e1 e2 = do
  eqv <- gets tc_equiv_manager
  modify (\tc -> tc { tc_equiv_manager = EM.add_equiv e1 e2 eqv })

em_is_equiv :: Expression -> Expression -> DefEqMethod ()
em_is_equiv e1 e2 = do
  eqv <- gets tc_equiv_manager  
  let (is_equiv,new_eqv) = EM.is_equiv e1 e2 eqv in do
    modify (\tc -> tc { tc_equiv_manager = new_eqv })
    if is_equiv then throwE True else return ()

{- extensions -}

lift_maybe :: (MonadPlus m) => Maybe a -> m a
lift_maybe = maybe mzero return

-- | Reduce terms 'e' of the form 'elim_k A C e p[A,b] (intro_k_i A b u)'
inductive_norm_ext :: Expression -> MaybeT TCMethod Expression
inductive_norm_ext e = do
  elim_infos <- liftM (iext_elim_infos . env_ind_ext . tc_env) get
  elim_fn_const <- lift_maybe $ maybe_constant (get_operator e)
  einfo@(ExtElimInfo ind_name lp_names num_params num_ACe num_indices k_target dep_elim) <-
    lift_maybe $ Map.lookup (const_name elim_fn_const) elim_infos
  guard $ genericLength (get_app_args e) >= num_ACe + num_indices + 1
  let major_idx = num_ACe + num_indices
      major = genericIndex (get_app_args e) major_idx in do
    (intro_app,comp_rule) <- find_comp_rule einfo elim_fn_const major
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
    find_comp_rule :: ExtElimInfo -> ConstantData -> Expression -> MaybeT TCMethod (Expression,CompRule)
    find_comp_rule einfo elim_fn_const major
      | eei_K_target einfo = do
        mb_result <- lift . runMaybeT $
                     (do intro_app <- to_intro_when_K einfo major
                         map_comp_rules <- liftM (iext_comp_rules . env_ind_ext . tc_env) get                                     
                         intro_app_op_const <- lift_maybe $ maybe_constant (get_operator intro_app)
                         comp_rule <- lift_maybe $ Map.lookup (const_name intro_app_op_const) map_comp_rules
                         return (intro_app,comp_rule))
        case mb_result of
          Nothing -> regular_comp_rule einfo elim_fn_const major
          Just result -> return result
      | otherwise = regular_comp_rule einfo elim_fn_const major
    regular_comp_rule :: ExtElimInfo -> ConstantData -> Expression -> MaybeT TCMethod (Expression,CompRule)                    
    regular_comp_rule einfo elim_fn_const major = do
      intro_app <- lift $ whnf major
      comp_rule <- is_intro_for (const_name elim_fn_const) intro_app
      return (intro_app,comp_rule)
    

-- | Return 'True' if 'e' is an introduction rule for an eliminator named 'elim'
is_intro_for :: Name -> Expression -> MaybeT TCMethod CompRule
is_intro_for elim_name e = do
  map_comp_rules <- liftM (iext_comp_rules . env_ind_ext . tc_env) get
  intro_fn_const <- lift_maybe $ maybe_constant (get_operator e)
  comp_rule <- lift_maybe $ Map.lookup (const_name intro_fn_const) map_comp_rules
  guard (cr_elim_name comp_rule == elim_name)
  return comp_rule

-- | For datatypes that support K-axiom, given e an element of that type, we convert (if possible)
-- to the default constructor. For example, if (e : a = a), then this method returns (eq.refl a)
to_intro_when_K :: ExtElimInfo -> Expression -> MaybeT TCMethod Expression
to_intro_when_K einfo e = do
  env <- gets tc_env
  assert (eei_K_target einfo) "to_intro_when_K should only be called when K_target holds" (return ())
  app_type <- lift $ infer_type e >>= whnf
  app_type_I <- return $ get_operator app_type
  app_type_I_const <- lift_maybe $ maybe_constant app_type_I
  guard (const_name app_type_I_const == eei_inductive_name einfo)
  new_intro_app <- lift_maybe $ mk_nullary_intro env app_type (eei_num_params einfo)
  new_type <- lift $ infer_type new_intro_app
  types_eq <- lift $ is_def_eq app_type new_type
  guard types_eq
  return new_intro_app

-- | If 'op_name' is the name of a non-empty inductive datatype, then return the
--   name of the first introduction rule. Return 'Nothing' otherwise.
get_first_intro :: Environment -> Name -> Maybe Name
get_first_intro env op_name = do
  mutual_idecls <- Map.lookup op_name (iext_ind_infos $ env_ind_ext env)
  InductiveDecl _ _ intro_rules <- find (\(InductiveDecl ind_name _ _) -> ind_name == op_name) (mid_idecls mutual_idecls)
  IntroRule ir_name _ <- find (\_ -> True) intro_rules
  return ir_name

mk_nullary_intro :: Environment -> Expression -> Integer -> Maybe Expression
mk_nullary_intro env app_type num_params = 
  let (op,args) = get_app_op_args app_type in do
    op_const <- maybe_constant op
    intro_name <- get_first_intro env (const_name op_const)
    return $ mk_app_seq (mk_constant intro_name (const_levels op_const)) (genericTake num_params args)

{- Quotient -}

quotient_norm_ext :: Expression -> MaybeT TCMethod Expression
quotient_norm_ext e = do
  env <- gets tc_env
  guard (env_quot_enabled env)
  fn <- lift_maybe $ maybe_constant (get_operator e)
  (mk_pos,arg_pos) <- if const_name fn == quot_lift then return (5,3) else
                        if const_name fn == quot_ind then return (4,3) else
                          fail "no quot comp rule applies"
  args <- return $ get_app_args e
  guard $ genericLength args > mk_pos
  mk <- lift $ whnf (genericIndex args mk_pos)
  case mk of
    App mk_as_app -> do
      mk_fn <- return $ get_operator mk
      mk_fn_const <- lift_maybe $ maybe_constant mk_fn
      guard $ const_name mk_fn_const == quot_mk
      let f = genericIndex args arg_pos
          elim_arity = mk_pos + 1
          extra_args = genericDrop elim_arity args in
        return $ mk_app_seq (mk_app f (app_arg mk_as_app)) extra_args
    _ -> fail "element of type 'quot' not constructed with 'quot.mk'"
    where
      quot_lift = mk_name ["lift","quot"]
      quot_ind = mk_name ["ind","quot"]
      quot_mk = mk_name ["mk","quot"]
