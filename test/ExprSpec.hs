module ExprSpec where
import Test.Hspec

import Kernel.Name.Internal
import Kernel.Level.Internal
import Kernel.Expr.Internal

mkType = mkSort mkLevelOne

getFreeVarRangeSpec =
  let e1 = mkConstant (mkName ["c1"]) []
      e2 = mkApp e1 (mkVar 1)
      e3 = mkSort mkZero
      e4 = mkLambdaDefault e3 e2
      e5 = mkPiDefault e3 e4 in do
    describe "getFreeVarRange" $ do
      it "should be 0 for constants" $ do
        getFreeVarRange e1 `shouldBe` 0
      it "should be 1+vIdx for Vars inside Apps" $ do
        getFreeVarRange e2 `shouldBe` 2
      it "should be 0 for sorts" $ do
        getFreeVarRange e3 `shouldBe` 0
      it "should decrement for each lambda" $ do
        getFreeVarRange e4 `shouldBe` 1
      it "should decrement for each pi" $ do
        getFreeVarRange e5 `shouldBe` 0


exprHasLevelParamSpec =
  let lp1 = mkLevelParam (mkName ["l1"])
      gp1 = mkGlobalLevel (mkName ["g1"])
      level1 = mkIteratedSucc (mkIMax lp1 mkLevelTwo) 2
      level2 = mkIteratedSucc (mkMax (mkSucc mkZero) gp1) 3
      const1 = mkConstant (mkName ["c1"]) [level1]
      const2 = mkConstant (mkName ["c2"]) [level2]
      const12 = mkConstant (mkName ["c12"]) [level1,level2]
      e1 = mkLambdaDefault mkProp const1
      e2 = mkPiDefault const2 const2
      e12 = mkPiDefault const12 e2
      e3 = mkPiDefault (mkSort lp1) const2 in do
    describe "exprHasLevelParam" $ do
      it "should be True for constants with level params" $ do
        exprHasLevelParam e1 `shouldBe` True
      it "should be False for constants with no level params" $ do
        exprHasLevelParam e2 `shouldBe` False
      it "should be True for constants with some level params" $ do
        exprHasLevelParam e12 `shouldBe` True
      it "should be True if there is a sort with a level param" $ do
        exprHasLevelParam e3 `shouldBe` True

instantiateSpec :: Spec
instantiateSpec =
  let c1 = mkConstant (mkName ["c1"]) []
      c2 = mkConstant (mkName ["c2"]) []

      e1 = mkLambdaDefault (mkApp c1 c2) (mkVar 1)
      subst1 = mkApp (mkVar 10) mkType
      ret1 = instantiate e1 subst1
      expectedRet1 = mkLambdaDefault (mkApp c1 c2) (mkApp (mkVar 11) mkType)

      e2 = mkLambdaDefault mkType (mkAppSeq (mkVar 0) [mkVar 1,mkVar 2])
      subst2 = c1
      ret2 = instantiate e2 subst2
      expectedRet2 = mkLambdaDefault mkType (mkAppSeq (mkVar 0) [c1,mkVar 1])

      ret3 = instantiate ret2 c2
      expectedRet3 = mkLambdaDefault mkType (mkAppSeq (mkVar 0) [c1,c2])

      ret4 = instantiate (mkPiDefault (mkVar 3) (mkVar 4)) (mkVar 0)
      expectedRet4 = mkPiDefault (mkVar 2) (mkVar 3)
  in do
    describe "instantiate" $ do
      it "should lift free vars in subst" $ do
        ret1 `shouldBe` expectedRet1
      it "should lift free vars in subst" $ do
        ret2 `shouldBe` expectedRet2
      it "should lift free vars in subst" $ do
        ret3 `shouldBe` expectedRet3
      it "should decrement untouched free vars in e" $ do
        ret4 `shouldBe` expectedRet4

instantiateLevelParamsSpec :: Spec
instantiateLevelParamsSpec =
  let lp1 = mkLevelParam (mkName ["l1"])
      gp1 = mkGlobalLevel (mkName ["g1"])
      level1 = mkIteratedSucc (mkIMax lp1 mkLevelTwo) 2
      level2 = mkIteratedSucc (mkMax (mkSucc mkZero) gp1) 3
      const1 = mkConstant (mkName ["c1"]) [level1]
      const2 = mkConstant (mkName ["c2"]) [level2]
      const12 = mkConstant (mkName ["c12"]) [level1,level2]
      e1 = mkLambdaDefault mkProp const1
      e2 = mkPiDefault const2 const2
      e12 = mkPiDefault const12 e2
      e3 = mkPiDefault (mkSort lp1) const2 in do
    describe "instantiateLevelParams" $ do
      it "sanity test" $ do
        instantiateLevelParams e1 [mkName ["l1"]] [level2] `shouldBe`
          (mkLambdaDefault mkProp (mkConstant (mkName ["c1"]) [mkIteratedSucc (mkIMax level2 mkLevelTwo) 2]))
      it "should work even if subst contains the same level params" $ do
        instantiateLevelParams e1 [mkName ["l1"]] [level1] `shouldBe`
          (mkLambdaDefault mkProp (mkConstant (mkName ["c1"]) [mkIteratedSucc (mkIMax level1 mkLevelTwo) 2]))


appSeqSpec :: Spec
appSeqSpec =
  let cs = map (\s -> mkConstant (mkName [s]) []) ["c1","c2","c3","c4"]

      e = mkApp (mkApp (mkApp (cs!!0) (cs!!1)) (cs!!2)) (cs!!3)
      op = getOperator e
      args = getAppArgs e
      e' = mkAppSeq op args

      s = mkLambdaDefault mkProp (mkVar 2)
  in do
    describe "appSeq" $ do
      it "mkAppSeq (getOperator e) (getAppArgs e) should yield e" $ do
        e `shouldBe` e'
      it "getOperator e = e if e is not app" $ do
        (getOperator s) `shouldBe` s
      it "getAppArgs e = [] if e is not app" $ do
        (getAppArgs s) `shouldBe` []

innerBodyOfLambdaSpec :: Spec
innerBodyOfLambdaSpec =
  let c = mkConstant (mkName ["c"]) []
      e = mkLambdaDefault mkProp (mkLambdaDefault mkType c) in do
    describe "innerBodyOfLambda" $ do
      it "should return body of nested lambdas" $ do
        (innerBodyOfLambda e) `shouldBe` c
      it "should do nothing on constants" $ do
        (innerBodyOfLambda (innerBodyOfLambda e)) `shouldBe` (innerBodyOfLambda e)


spec :: Spec
spec = do
  getFreeVarRangeSpec
  exprHasLevelParamSpec
  instantiateSpec
  instantiateLevelParamsSpec
  appSeqSpec
  innerBodyOfLambdaSpec
