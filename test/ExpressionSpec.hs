module ExpressionSpec where
import Test.Hspec

import Name
import Level
import Expression





get_free_var_range_spec =
  let e1 = mk_constant (mk_name ["c1"]) []
      e2 = mk_app e1 (mk_var 1)
      e3 = mk_Prop
      e4 = mk_lambda_anon e3 e2
      e5 = mk_pi_anon e3 e4 in do
    describe "get_free_var_range" $ do
      it "should be 0 for constants" $ do
        get_free_var_range e1 `shouldBe` 0
      it "should be 1+v_idx for Vars inside Apps" $ do
        get_free_var_range e2 `shouldBe` 2
      it "should be 0 for sorts" $ do
        get_free_var_range e3 `shouldBe` 0
      it "should decrement for each lambda" $ do
        get_free_var_range e4 `shouldBe` 1
      it "should decrement for each pi" $ do
        get_free_var_range e5 `shouldBe` 0


expr_has_param_univ_spec =
  let lp1 = mk_level_param (mk_name ["l1"])
      gp1 = mk_global_univ (mk_name ["g1"])
      level1 = mk_iterated_succ (mk_imax lp1 mk_level_two) 2
      level2 = mk_iterated_succ (mk_max (mk_succ mk_zero) gp1) 3
      const1 = mk_constant (mk_name ["c1"]) [level1]
      const2 = mk_constant (mk_name ["c2"]) [level2]
      const12 = mk_constant (mk_name ["c12"]) [level1,level2]
      e1 = mk_lambda_anon mk_Prop const1
      e2 = mk_pi_anon const2 const2
      e12 = mk_pi_anon const12 e2
      e3 = mk_pi_anon (mk_sort lp1) const2 in do
    describe "expr_has_param_univ" $ do
      it "should be True for constants with level params" $ do
        expr_has_param_univ e1 `shouldBe` True        
      it "should be False for constants with no level params" $ do
        expr_has_param_univ e2 `shouldBe` False
      it "should be True for constants with some level params" $ do
        expr_has_param_univ e12 `shouldBe` True
      it "should be True if there is a sort with a level param" $ do
        expr_has_param_univ e3 `shouldBe` True

instantiate_spec :: Spec
instantiate_spec =
  let c1 = mk_constant (mk_name ["c1"]) []
      c2 = mk_constant (mk_name ["c2"]) []

      e1 = mk_lambda_anon (mk_app c1 c2) (mk_var 1)
      subst1 = mk_app (mk_var 10) mk_Type
      ret1 = instantiate e1 subst1
      expected_ret1 = mk_lambda_anon (mk_app c1 c2) (mk_app (mk_var 11) mk_Type)

      e2 = mk_lambda_anon mk_Type (mk_app_seq (mk_var 0) [mk_var 1,mk_var 2])
      subst2 = c1
      ret2 = instantiate e2 subst2
      expected_ret2 = mk_lambda_anon mk_Type (mk_app_seq (mk_var 0) [c1,mk_var 1])

      ret3 = instantiate ret2 c2
      expected_ret3 = mk_lambda_anon mk_Type (mk_app_seq (mk_var 0) [c1,c2])

      ret4 = instantiate (mk_pi_anon (mk_var 3) (mk_var 4)) (mk_var 0)
      expected_ret4 = mk_pi_anon (mk_var 2) (mk_var 3)
  in do
    describe "instantiate" $ do
      it "should lift free vars in subst" $ do
        ret1 `shouldBe` expected_ret1
      it "should lift free vars in subst" $ do        
        ret2 `shouldBe` expected_ret2
      it "should lift free vars in subst" $ do        
        ret3 `shouldBe` expected_ret3
      it "should decrement untouched free vars in e" $ do        
        ret4 `shouldBe` expected_ret4

instantiate_univ_params_spec :: Spec
instantiate_univ_params_spec =
  let lp1 = mk_level_param (mk_name ["l1"])
      gp1 = mk_global_univ (mk_name ["g1"])
      level1 = mk_iterated_succ (mk_imax lp1 mk_level_two) 2
      level2 = mk_iterated_succ (mk_max (mk_succ mk_zero) gp1) 3
      const1 = mk_constant (mk_name ["c1"]) [level1]
      const2 = mk_constant (mk_name ["c2"]) [level2]
      const12 = mk_constant (mk_name ["c12"]) [level1,level2]
      e1 = mk_lambda_anon mk_Prop const1
      e2 = mk_pi_anon const2 const2
      e12 = mk_pi_anon const12 e2
      e3 = mk_pi_anon (mk_sort lp1) const2 in do
    describe "instantiate_univ_params" $ do
      it "sanity test" $ do
        instantiate_univ_params e1 [mk_name ["l1"]] [level2] `shouldBe`
          (mk_lambda_anon mk_Prop (mk_constant (mk_name ["c1"]) [mk_iterated_succ (mk_imax level2 mk_level_two) 2]))
      it "should work even if subst contains the same level params" $ do
        instantiate_univ_params e1 [mk_name ["l1"]] [level1] `shouldBe`
          (mk_lambda_anon mk_Prop (mk_constant (mk_name ["c1"]) [mk_iterated_succ (mk_imax level1 mk_level_two) 2]))


app_seq_spec :: Spec
app_seq_spec =
  let cs = map (\s -> mk_constant (mk_name [s]) []) ["c1","c2","c3","c4"]

      e = mk_app (mk_app (mk_app (cs!!0) (cs!!1)) (cs!!2)) (cs!!3)
      op = get_operator e
      args = get_app_args e
      e' = mk_app_seq op args

      s = mk_lambda_anon mk_Prop (mk_var 2)
  in do
    describe "app_seq" $ do
      it "mk_app_seq (get_operator e) (get_app_args e) should yield e" $ do
        e `shouldBe` e'
      it "get_operator e = e if e is not app" $ do
        (get_operator s) `shouldBe` s
      it "get_app_args e = [] if e is not app" $ do
        (get_app_args s) `shouldBe` []

body_of_lambda_spec :: Spec
body_of_lambda_spec =
  let c = mk_constant (mk_name ["c"]) []
      e = mk_lambda_anon mk_Prop (mk_lambda_anon mk_Type c) in do
    describe "body_of_lambda" $ do
      it "should return body of nested lambdas" $ do
        (body_of_lambda e) `shouldBe` c
      it "should do nothing on constants" $ do
        (body_of_lambda (body_of_lambda e)) `shouldBe` (body_of_lambda e)


spec :: Spec
spec = do
  get_free_var_range_spec
  expr_has_param_univ_spec
  instantiate_spec
  instantiate_univ_params_spec
  app_seq_spec
  body_of_lambda_spec
