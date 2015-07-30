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



              



spec :: Spec
spec = do
  infer_lambda1
  infer_app1
  infer_const1
