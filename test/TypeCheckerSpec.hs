module TypeCheckerSpec where
import Test.Hspec

import Name
import Level
import Expression
import Environment
import TypeChecker

infer_lambda1 =
  let env = empty_environment
      lam1 = mk_lambda_anon mk_Prop mk_Prop
      result1 = tc_run env [] 0 (infer_type lam1)
  in
  describe "infer_lambda1" $ do
    it "basic" $ do
      case result1 of
        Right e ->
          case e of
            Pi pi -> do
              (binding_domain pi) `shouldBe` mk_Prop              
              (binding_body pi) `shouldBe` mk_Type
    
infer_app1 =
  let env = empty_environment
      lam1 = mk_lambda_anon mk_Type mk_Type
      app1 = mk_app lam1 mk_Prop
      result1 = tc_run env [] 0 (infer_type app1)
  in
  describe "infer_app1" $ do
    it "basic" $ do
      case result1 of
        Right e -> e `shouldBe` mk_Type2

infer_const1 =
  let env = empty_environment
      ax_type = mk_pi_anon mk_Type mk_Prop
      ax_name = mk_name ["ax1"]
      decl = mk_axiom ax_name [] ax_type in
  case TypeChecker.check env decl of
    Right cdecl ->
      let new_env = env_add env cdecl in
      describe "infer_const1" $ do
        it "basic" $ do
          case tc_run new_env [] 0 (infer_type (mk_constant ax_name [])) of
            Right e -> e `shouldBe` ax_type


hpass = return ()
hfail = True `shouldBe` False

trigger_exceptions = describe "TypeChecker exceptions" $ do
  it "UndefGlobalUniv" $ do
    let n = mk_name ["undef"]
        uni = mk_global_univ n
        d = mk_axiom no_name [] (mk_sort uni) in
      case check empty_environment d of
        Left err -> err `shouldBe` (UndefGlobalUniv n)
  it "UndefLevelParam" $ do
    let n = mk_name ["undef"]
        lp = mk_level_param n
        d = mk_axiom no_name [] (mk_sort lp) in
      case check empty_environment d of
        Left err -> err `shouldBe` (UndefLevelParam n)
  it "TypeExpected" $ do
    let e = mk_lambda_anon mk_Prop mk_Prop
        t = mk_pi_anon mk_Prop mk_Type
        d = mk_axiom no_name [] e in
      case check empty_environment d of
        Left (TypeExpected _) -> hpass
        _ -> hfail
  it "FunctionExpected" $ do
    let d = mk_axiom no_name [] (mk_app mk_Prop mk_Prop) in
      case check empty_environment d of
        Left (FunctionExpected _) -> hpass
        _ -> hfail
  it "TypeMismatchAtApp" $ do
    let e = mk_app (mk_lambda_anon mk_Prop mk_Prop) mk_Prop
        d = mk_axiom no_name [] e in
      case check empty_environment d of
        Left (TypeMismatchAtApp _ _) -> hpass
        _ -> hfail
  it "TypeMismatchAtDef" $ do
    let e = mk_lambda_anon mk_Prop mk_Prop
        t = mk_pi_anon mk_Type mk_Type
        d = mk_definition empty_environment no_name [] t e in
      case check empty_environment d of
        Left (TypeMismatchAtDef _ _) -> hpass
  it "DeclHasFreeVars" $ do
    let d = mk_axiom no_name [] (mk_var 0) in
      case check empty_environment d of
        Left (DeclHasFreeVars _) -> hpass
  it "DeclHasLocals" $ do
    let d = mk_axiom no_name [] (mk_local no_name no_name mk_Prop BinderDefault) in
      case check empty_environment d of
        Left (DeclHasLocals _) -> hpass
  it "NameAlreadyDeclared" $ do
    let d = mk_axiom no_name [] mk_Prop in
      case check empty_environment d of
        Right cdecl -> case check (env_add empty_environment cdecl) d of
          Left (NameAlreadyDeclared _) -> hpass
  it "DuplicateLevelParamName" $ do
    let n = mk_name ["undef"]
        lp = mk_level_param n
        d = mk_axiom no_name [n,n] (mk_sort lp) in
      case check empty_environment d of
        Left DuplicateLevelParamName -> hpass
        _ -> hfail
  it "ConstNotFound" $ do
    let c = mk_constant (mk_name ["not-found"]) []
        d = mk_axiom no_name [] c in
      case check empty_environment d of
        Left (ConstNotFound _) -> hpass
        _ -> hfail
  it "ConstHasWrongNumLevels" $ do
    let c = mk_constant no_name [mk_zero]
        d1 = mk_axiom no_name [] mk_Prop
        d2 = mk_axiom (mk_name ["n"]) [] c
      in
      case check empty_environment d1 of
        Right cdecl -> case check (env_add empty_environment cdecl) d2 of
          Left (ConstHasWrongNumLevels _ _ _) -> hpass
          _ -> hfail
    
spec :: Spec
spec = do
  infer_lambda1
  infer_app1
  infer_const1
  trigger_exceptions
