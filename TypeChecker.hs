module TypeChecker where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Except
import Data.List (nub)
import Debug.Trace

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
               | WrongNumUnivParams
               | KernelError
               | NYI
                 deriving Show

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
  sort <- infer_type (decl_type d)
  ensure_sort sort
  maybe (return ()) (check_val_matches_ty (decl_type d)) (decl_mb_val d)
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
      tc_assert (length d_level_names == length c_levels) WrongNumUnivParams
      mapM_ (\level -> check_level level) c_levels
      return $ instantiate_univ_params (decl_type d) d_level_names c_levels

mk_local_for :: BindingData -> TCMethod LocalData
mk_local_for bind = do
  next_id <- gensym
  return $ mk_local_data (mk_system_name next_id) (binding_name bind) (binding_domain bind) (binding_info bind)
  
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
  App app -> let (fn,arg) = app_fn_arg app in unfold_name_core w fn >>= return . flip mk_app arg
  _ -> unfold_name_core w e
        
unfold_name_core :: Integer -> Expression -> TCMethod Expression
unfold_name_core w e = case e of
  Constant const -> do
    tc <- ask
    maybe (return e) 
      (\d -> case decl_mb_val d of
          Just decl_val
            | not (is_opaque d) && decl_weight d >= w && length (const_levels const) == length (decl_level_names d)
              -> unfold_name_core w (instantiate_univ_params decl_val (decl_level_names d) $ const_levels const)
          _ -> return e)
      (lookup_declaration (tc_env tc) (const_name const))
  _ -> return e

-- TODO iterate over env's normalizer extensions
normalize_ext e = return Nothing

-- is_def_eq

is_def_eq :: Expression -> Expression -> TCMethod Bool
is_def_eq t s = do
  success <- runExceptT (is_def_eq_main t s)
  case success of
    Left answer -> return answer
    Right () -> return False

deq_commit_to :: DefEqMethod () -> DefEqMethod ()
deq_commit_to defeq = defeq >> throwE False
                                    
-- This exception means we know if they are equal or not
type DefEqMethod = ExceptT Bool TCMethod

-- deq_fail = lift . tc_fail
deq_assert b err = lift $ tc_assert b err

try_if :: Bool -> DefEqMethod () -> DefEqMethod ()
try_if b check = if b then check else return ()

deq_true_as_continue :: TCMethod Bool -> DefEqMethod ()
deq_true_as_continue test = do
  yes <- lift test
  case yes of
    True -> return ()
    False -> throwE False

pass :: DefEqMethod()
pass = return ()

is_def_eq_main :: Expression -> Expression -> DefEqMethod ()
is_def_eq_main t s = do
  quick_is_def_eq t s
  t_n <- lift $ whnf_core t
  s_n <- lift $ whnf_core s
  try_if (t_n /= t || s_n /= s) (quick_is_def_eq t_n s_n)
  (t_n,s_n) <- reduce_def_eq t_n s_n

  case (t_n,s_n) of
    (Constant const1, Constant const2) | const_name const1 == const_name const2 ->
      is_def_eq_levels (const_levels const1) (const_levels const2)
    (Local local1, Local local2) | local_name local1 == local_name local2 ->
      throwE True
    _ -> pass

  is_def_eq_app t_n s_n
  eta_expansion t_n s_n
  is_def_proof_irrel t_n s_n

reduce_def_eq :: Expression -> Expression -> DefEqMethod (Expression,Expression)
reduce_def_eq t s = do
  (t,s,status) <- lazy_delta_reduction t s >>= uncurry ext_reduction_step
  case status of
    DefUnknown -> return (t,s)
    Continue -> reduce_def_eq t s

-- TODO
ext_reduction_step t s = return (t,s,DefUnknown)

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
    Just d | is_definition d && not (is_opaque d) -> Just d
    _ -> Nothing
  _ -> Nothing

-- TODO ugly
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
    EQ -> do t_dn <- lift (unfold_names (decl_weight d_s + 1) t >>= whnf_core)
             s_dn <- lift (unfold_names (decl_weight d_t + 1) s >>= whnf_core)
             return (t_dn,s_dn)
    
is_def_eq_app :: Expression -> Expression -> DefEqMethod ()
is_def_eq_app t s = case (t,s) of
  (App app1,App app2) -> do deq_true_as_continue (is_def_eq (app_fn app1) (app_fn app2))
                            args_eq <- lift $ is_def_eq (app_arg app1) (app_arg app2)
                            throwE args_eq
  _ -> pass
  
eta_expansion :: Expression -> Expression -> DefEqMethod ()
eta_expansion t s = eta_expansion_core t s >> eta_expansion_core s t

-- TODO not yet implemented
eta_expansion_core :: Expression -> Expression -> DefEqMethod ()
eta_expansion_core t s = return ()

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
  (Sort sort1, Sort sort2) -> throwE (is_def_eq_level (sort_level sort1) (sort_level sort2))
  _ -> return ()

is_def_eq_binding bind1 bind2 = do
  deq_true_as_continue (is_def_eq (binding_domain bind1) (binding_domain bind2))
  next_id <- lift gensym
  local <- return $ mk_local (mk_system_name next_id) (binding_name bind1) (binding_domain bind1) (binding_info bind1)
  is_def_eq_main (instantiate (binding_body bind1) local) (instantiate (binding_body bind2) local)

is_def_eq_level l1 l2 = l1 == l2 || normalize_level l1 == normalize_level l2
is_def_eq_levels ls1 ls2 = if (all (True==) (map (uncurry is_def_eq_level) (zip ls1 ls2))) then throwE True else return ()
                          



-----
gensym :: StateT Integer (ReaderT TypeChecker (Either TypeError)) Integer
gensym = do
  n <- get
  put (n+1)
  return n

-- TODO make sure only this module can create these
mk_certified_declaration env d = CertifiedDeclaration env d
