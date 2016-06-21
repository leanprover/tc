module TypeCheckerSpec where
import Test.Hspec

import Kernel.Name.Internal
import Kernel.Level.Internal
import Kernel.Expr.Internal
import Kernel.TypeChecker.Internal

mkType = mkSort mkLevelOne
mkType2 = mkSort mkLevelTwo

inferLambda1 =
  let env = mkStdEnv
      lam1 = mkLambdaDefault mkProp mkProp
      result1 = tcRun env [] 0 (inferType lam1)
  in
  describe "inferLambda1" $ do
    it "basic" $ do
      case result1 of
        Right e ->
          case e of
            Pi pi -> do
              (bindingDomain pi) `shouldBe` mkProp
              (bindingBody pi) `shouldBe` mkType

inferApp1 =
  let env = mkStdEnv
      lam1 = mkLambdaDefault mkType mkType
      app1 = mkApp lam1 mkProp
      result1 = tcRun env [] 0 (inferType app1)
  in
  describe "inferApp1" $ do
    it "basic" $ do
      case result1 of
        Right e -> e `shouldBe` mkType2

inferConst1 =
  let env = mkStdEnv
      axType = mkPiDefault mkType mkProp
      axName = mkName ["ax1"] in
  case envAddAxiom axName [] axType env of
    Right newEnv ->
      describe "inferConst1" $ do
        it "basic" $ do
          case tcRun newEnv [] 0 (inferType (mkConstant axName [])) of
            Right e -> e `shouldBe` axType


hpass = return ()
hfail = True `shouldBe` False

triggerExceptions = describe "TypeChecker exceptions" $ do
  it "UndefGlobalLevel" $ do
    let n = mkName ["undef"]
        uni = mkGlobalLevel n
        d = mkAxiom noName [] (mkSort uni) in
      case check mkStdEnv d of
        Left err -> err `shouldBe` (UndefGlobalLevel n)
  it "UndefLevelParam" $ do
    let n = mkName ["undef"]
        lp = mkLevelParam n
        d = mkAxiom noName [] (mkSort lp) in
      case check mkStdEnv d of
        Left err -> err `shouldBe` (UndefLevelParam n)
  it "TypeExpected" $ do
    let e = mkLambdaDefault mkProp mkProp
        t = mkPiDefault mkProp mkType
        d = mkAxiom noName [] e in
      case check mkStdEnv d of
        Left (TypeExpected _) -> hpass
        _ -> hfail
  it "FunctionExpected" $ do
    let d = mkAxiom noName [] (mkApp mkProp mkProp) in
      case check mkStdEnv d of
        Left (FunctionExpected _) -> hpass
        _ -> hfail
  it "TypeMismatchAtApp" $ do
    let e = mkApp (mkLambdaDefault mkProp mkProp) mkProp
        d = mkAxiom noName [] e in
      case check mkStdEnv d of
        Left (TypeMismatchAtApp _ _) -> hpass
        _ -> hfail
  it "TypeMismatchAtDef" $ do
    let e = mkLambdaDefault mkProp mkProp
        t = mkPiDefault mkType mkType
        d = mkDefinition mkStdEnv noName [] t e in
      case check mkStdEnv d of
        Left (TypeMismatchAtDef _ _) -> hpass
  it "DeclHasFreeVars" $ do
    let d = mkAxiom noName [] (mkVar 0) in
      case check mkStdEnv d of
        Left (DeclHasFreeVars _) -> hpass
  it "DeclHasLocals" $ do
    let d = mkAxiom noName [] (mkLocal noName noName mkProp BinderDefault) in
      case check mkStdEnv d of
        Left (DeclHasLocals _) -> hpass
  it "NameAlreadyDeclared" $ do
    case envAddAxiom noName [] mkProp mkStdEnv of
      Right newEnv -> case envAddAxiom noName [] mkProp newEnv of
        Left (NameAlreadyDeclared _) -> hpass
  it "DuplicateLevelParamName" $ do
    let n = mkName ["undef"]
        lp = mkLevelParam n
        d = mkAxiom noName [n,n] (mkSort lp) in
      case check mkStdEnv d of
        Left DuplicateLevelParamName -> hpass
        _ -> hfail
  it "ConstNotFound" $ do
    let c = mkConstant (mkName ["not-found"]) []
        d = mkAxiom noName [] c in
      case check mkStdEnv d of
        Left (ConstNotFound _) -> hpass
        _ -> hfail
  it "ConstHasWrongNumLevels" $ do
    case envAddAxiom noName [] mkProp mkStdEnv of
      Right newEnv -> case envAddAxiom (mkName ["n"]) [] (mkConstant noName [mkZero]) newEnv of
          Left (ConstHasWrongNumLevels _ _ _) -> hpass
          _ -> hfail

spec :: Spec
spec = do
  inferLambda1
  inferApp1
  inferConst1
  triggerExceptions
