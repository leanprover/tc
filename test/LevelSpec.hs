module LevelSpec where
import Test.Hspec

import Name
import Level


has_param_spec :: Spec
has_param_spec = do
  let lp1 = mk_level_param (mk_name ["l1"])
      lp2 = mk_level_param (mk_name ["l2"])
      gp1 = mk_global_univ (mk_name ["g1"])
      gp2 = mk_global_univ (mk_name ["g2"])            
      l0 = mk_iterated_succ gp1 3
      l1 = mk_iterated_succ lp1 4
      l2 = mk_iterated_succ (mk_max lp1 gp1) 2
      l3 = mk_iterated_succ (mk_max gp1 gp2) 2
      l4 = mk_max gp1 (mk_max gp2 mk_zero)
      l5 = mk_imax gp1 (mk_imax lp1 lp2) in do
    describe "has_param" $ do
        it "global should not count" $ do
          (has_param l0) `shouldBe` False
        it "should recurse under Succ" $ do
          (has_param l1) `shouldBe` True
        it "should recurse under succ and max when true" $ do
          (has_param l2) `shouldBe` True
        it "should recurse under succ and max when false" $ do
          (has_param l3) `shouldBe` False
        it "should recurse under nested max when false" $ do
          (has_param l4) `shouldBe` False
        it "should recurse under nested max when true" $ do
          (has_param l5) `shouldBe` True

replace_in_level_spec :: Spec
replace_in_level_spec =
  let f1 = (\level -> case level of
              LevelParam param -> Just (GlobalLevel param)
              _ -> Nothing)
      f2 = (\level -> Just (mk_succ level))
      gp1 = mk_global_univ (mk_name ["l1"])
      lp2 = mk_level_param (mk_name ["l2"])
      gp2 = mk_global_univ (mk_name ["l2"])            
      level = mk_iterated_succ (mk_max gp1 (mk_imax lp2 (mk_iterated_succ mk_zero 3))) 2
      ret1 = replace_in_level f1 level
      expected1 = mk_iterated_succ (mk_max gp1 (mk_imax gp2 (mk_iterated_succ mk_zero 3))) 2      
      ret2 = replace_in_level f2 level
      expected2 = mk_iterated_succ (mk_max gp1 (mk_imax lp2 (mk_iterated_succ mk_zero 3))) 3 in do
    describe "replace_in_level" $ do
        it "should only replace when `f` returns Just" $ do
          ret1 `shouldBe` expected1
        it "should not recurse if f always returns Just" $ do
          ret2 `shouldBe` expected2


instantiate_level_spec :: Spec
instantiate_level_spec =
  let lp_names = map (\s -> mk_name [s]) ["lp1","lp2"]
      lp1 = mk_level_param (mk_name ["lp1"])
      lp2 = mk_level_param (mk_name ["lp2"])
      lp3 = mk_level_param (mk_name ["lp3"])
      old_level = mk_max lp1 (mk_max lp2 lp3)

      new_levels1 = [mk_zero,lp3]
      new_level1 = instantiate_level lp_names new_levels1 old_level
      expected_new_level1 = lp3

      new_levels2 = [lp2,lp1]
      new_level2 = instantiate_level lp_names new_levels2 old_level
      expected_new_level2 = mk_max lp2 (mk_max lp1 lp3)
  in do
    describe "instantiate_level" $ do
        it "sanity test" $ do
          new_level1 `shouldBe` expected_new_level1
        it "should work when substituting existing level param" $ do
          new_level2 `shouldBe` expected_new_level2
    
    
levels_misc_spec :: Spec
levels_misc_spec =
  let zero = mk_zero
      one = mk_succ zero
      two = mk_succ one
      p1 = mk_level_param (mk_name ["p1"])
      p2 = mk_level_param (mk_name ["p2"])      
  in describe "levels misc" $ do
    it "basic" $ do
      (mk_max one two) `shouldBe` two
      (mk_imax one two) `shouldBe` two
      (mk_imax two zero) `shouldBe` zero
      (mk_imax p1 zero) `shouldBe` zero
      (mk_max zero p1) `shouldBe` p1
      (mk_max p1 zero) `shouldBe` p1
      (mk_max p1 one) `shouldNotBe` p1
      level_equiv one (mk_succ zero) `shouldBe` True
      level_equiv zero two `shouldBe` False
      level_equiv zero p2 `shouldBe` False
    it "should normalize max" $ do
      (level_equiv (mk_succ p2) (mk_max p2 (mk_succ p2))) `shouldBe` True
      (level_equiv (mk_max p1 p2) (mk_max p2 p1)) `shouldBe` True
    it "should not normalize imax" $ do
      level_equiv (mk_imax p1 p2) (mk_imax p2 p1) `shouldBe` False
    it "mk_imax should call mk_max" $ do
      level_equiv (mk_imax (mk_succ p1) (mk_succ p2)) (mk_imax (mk_succ p2) (mk_succ p1)) `shouldBe` True

normalize_spec1 :: Spec
normalize_spec1 =
  let u = mk_global_univ (mk_name ["u"])
      v = mk_global_univ (mk_name ["v"])
      z = mk_zero in do
    describe "normalize1" $ do
      it "max should ignore zeros" $ do
        (normalize_level $ mk_max z (mk_max u (mk_succ z)))
          `shouldBe`
          (mk_max (mk_succ z) u)
      it "basic1" $ do
        (normalize_level $ mk_max (mk_max (mk_succ v) u) (mk_max v (mk_succ u)))
          `shouldBe`
          (mk_max (mk_succ u) (mk_succ v))
      it "basic" $ do
        (normalize_level $ mk_max (mk_succ mk_zero) u) `shouldBe` (mk_max (mk_succ mk_zero) u)
      it "basic2" $ do
        (normalize_level $ mk_max (mk_succ (mk_max (mk_succ v) u)) (mk_max v (mk_succ (mk_succ u))))
          `shouldBe`
          (mk_max (mk_succ (mk_succ u)) (mk_succ (mk_succ v)))
        
level_leq_spec1 :: Spec
level_leq_spec1 = do
  let u = mk_level_param (mk_name ["u"]) in
    describe "level_leq1" $ do
      it "should work with max on the rhs" $ do
        level_leq u (mk_max (mk_succ mk_zero) u) `shouldBe` True

spec :: Spec
spec = do
  has_param_spec
  replace_in_level_spec
  instantiate_level_spec
  levels_misc_spec
  normalize_spec1
  level_leq_spec1
  
