module LevelSpec where
import Test.Hspec

import Kernel.Name.Internal
import Kernel.Level.Internal

levelHasParamSpec :: Spec
levelHasParamSpec = do
  let lp1 = mkLevelParam (mkName ["l1"])
      lp2 = mkLevelParam (mkName ["l2"])
      gp1 = mkGlobalLevel (mkName ["g1"])
      gp2 = mkGlobalLevel (mkName ["g2"])
      l0 = mkIteratedSucc gp1 3
      l1 = mkIteratedSucc lp1 4
      l2 = mkIteratedSucc (mkMax lp1 gp1) 2
      l3 = mkIteratedSucc (mkMax gp1 gp2) 2
      l4 = mkMax gp1 (mkMax gp2 mkZero)
      l5 = mkIMax gp1 (mkIMax lp1 lp2) in do
    describe "levelHasParam" $ do
        it "global should not count" $ do
          (levelHasParam l0) `shouldBe` False
        it "should recurse under Succ" $ do
          (levelHasParam l1) `shouldBe` True
        it "should recurse under succ and max when true" $ do
          (levelHasParam l2) `shouldBe` True
        it "should recurse under succ and max when false" $ do
          (levelHasParam l3) `shouldBe` False
        it "should recurse under nested max when false" $ do
          (levelHasParam l4) `shouldBe` False
        it "should recurse under nested max when true" $ do
          (levelHasParam l5) `shouldBe` True

replaceInLevelSpec :: Spec
replaceInLevelSpec =
  let f1 = (\level -> case level of
              LevelParam param -> Just (GlobalLevel param)
              _ -> Nothing)
      f2 = (\level -> Just (mkSucc level))
      gp1 = mkGlobalLevel (mkName ["l1"])
      lp2 = mkLevelParam (mkName ["l2"])
      gp2 = mkGlobalLevel (mkName ["l2"])
      level = mkIteratedSucc (mkMax gp1 (mkIMax lp2 (mkIteratedSucc mkZero 3))) 2
      ret1 = replaceInLevel f1 level
      expected1 = mkIteratedSucc (mkMax gp1 (mkIMax gp2 (mkIteratedSucc mkZero 3))) 2
      ret2 = replaceInLevel f2 level
      expected2 = mkIteratedSucc (mkMax gp1 (mkIMax lp2 (mkIteratedSucc mkZero 3))) 3 in do
    describe "replaceInLevel" $ do
        it "should only replace when `f` returns Just" $ do
          ret1 `shouldBe` expected1
        it "should not recurse if f always returns Just" $ do
          ret2 `shouldBe` expected2


instantiateLevelSpec :: Spec
instantiateLevelSpec =
  let lpNames = map (\s -> mkName [s]) ["lp1","lp2"]
      lp1 = mkLevelParam (mkName ["lp1"])
      lp2 = mkLevelParam (mkName ["lp2"])
      lp3 = mkLevelParam (mkName ["lp3"])
      oldLevel = mkMax lp1 (mkMax lp2 lp3)

      newLevels1 = [mkZero,lp3]
      newLevel1 = instantiateLevel lpNames newLevels1 oldLevel
      expectedNewLevel1 = lp3

      newLevels2 = [lp2,lp1]
      newLevel2 = instantiateLevel lpNames newLevels2 oldLevel
      expectedNewLevel2 = mkMax lp2 (mkMax lp1 lp3)
  in do
    describe "instantiateLevel" $ do
        it "sanity test" $ do
          newLevel1 `shouldBe` expectedNewLevel1
        it "should work when substituting existing level param" $ do
          newLevel2 `shouldBe` expectedNewLevel2


levelsMiscSpec :: Spec
levelsMiscSpec =
  let zero = mkZero
      one = mkSucc zero
      two = mkSucc one
      p1 = mkLevelParam (mkName ["p1"])
      p2 = mkLevelParam (mkName ["p2"])
  in describe "levels misc" $ do
    it "basic" $ do
      (mkMax one two) `shouldBe` two
      (mkIMax one two) `shouldBe` two
      (mkIMax two zero) `shouldBe` zero
      (mkIMax p1 zero) `shouldBe` zero
      (mkMax zero p1) `shouldBe` p1
      (mkMax p1 zero) `shouldBe` p1
      (mkMax p1 one) `shouldNotBe` p1
      levelEquiv one (mkSucc zero) `shouldBe` True
      levelEquiv zero two `shouldBe` False
      levelEquiv zero p2 `shouldBe` False
    it "should normalize max" $ do
      (levelEquiv (mkSucc p2) (mkMax p2 (mkSucc p2))) `shouldBe` True
      (levelEquiv (mkMax p1 p2) (mkMax p2 p1)) `shouldBe` True
    it "should not normalize imax" $ do
      levelEquiv (mkIMax p1 p2) (mkIMax p2 p1) `shouldBe` False
    it "mkIMax should call mkMax" $ do
      levelEquiv (mkIMax (mkSucc p1) (mkSucc p2)) (mkIMax (mkSucc p2) (mkSucc p1)) `shouldBe` True

normalizeSpec1 :: Spec
normalizeSpec1 =
  let u = mkGlobalLevel (mkName ["u"])
      v = mkGlobalLevel (mkName ["v"])
      z = mkZero
      one = mkSucc z
      two = mkSucc one in do
    describe "normalize1" $ do
      it "max should ignore zeros" $ do
        (normalizeLevel $ mkMax z (mkMax u (mkSucc z)))
          `shouldBe`
          (mkMax (mkSucc z) u)
      it "basic1" $ do
        (normalizeLevel $ mkMax (mkMax (mkSucc v) u) (mkMax v (mkSucc u)))
          `shouldBe`
          (mkMax (mkSucc u) (mkSucc v))
      it "basic" $ do
        (normalizeLevel $ mkMax (mkSucc mkZero) u) `shouldBe` (mkMax (mkSucc mkZero) u)
      it "basic2" $ do
        (normalizeLevel $ mkMax (mkSucc (mkMax (mkSucc v) u)) (mkMax v (mkSucc (mkSucc u))))
          `shouldBe`
          (mkMax (mkSucc (mkSucc u)) (mkSucc (mkSucc v)))
      it "should remove irrelevant explicit levels" $ do
        (normalizeLevel $ mkMax (mkSucc u) (mkMax (mkMax u one) (mkMax one u)))
          `shouldBe`
          (mkSucc u)

levelNotBiggerThanSpec1 :: Spec
levelNotBiggerThanSpec1 = do
  let u = mkLevelParam (mkName ["u"]) in
    describe "levelNotBiggerThan" $ do
      it "should work with max on the rhs" $ do
        levelNotBiggerThan u (mkMax (mkSucc mkZero) u) `shouldBe` True

spec :: Spec
spec = do
  levelHasParamSpec
  replaceInLevelSpec
  instantiateLevelSpec
  levelsMiscSpec
  normalizeSpec1
  levelNotBiggerThanSpec1
