module InductiveSpec where
import Test.Hspec

import Name
import Level
import Expression
import Environment
import TypeChecker
import Inductive

{-
unit : Type.{1}
unit.star : unit
unit.rec : Π {C : unit → Type}, C unit.star → (Π (n : unit), C n)
-}
unit_spec = 
  let unit_name = mk_name ["unit"]
      unit_const = mk_constant (mk_name ["unit"]) []
      star_name = mk_name ["star","unit"]
      unit_decls = [InductiveDecl
                    unit_name
                    mk_Type
                    [IntroRule star_name unit_const]]
      star_const = mk_constant (mk_name ["star","unit"]) []
      rec_const = mk_constant (mk_name ["rec","unit"]) [mk_level_param (mk_name ["l1"])]
      c = mk_lambda_anon unit_const unit_const
      unit_rec_example = mk_app_seq rec_const [c,star_const,star_const] in
   describe "Inductive processing of unit" $ do
     let unit_result = ind_run add_inductive_core empty_environment [] 0 unit_decls
         unit_eval = fst unit_result
         unit_exec = snd unit_result
       in
      describe "check_inductive_types" $ do
        it "should not throw an error" $ do
          unit_eval `shouldBe` (Right ())
        it "should be at level 1" $ do
          m_it_levels unit_exec `shouldBe` [mk_level_one]
        it "should have 1 it_num_arg" $ do
          m_it_num_args unit_exec `shouldBe` [0]
        it "should not have any param_consts" $ do
          m_param_consts unit_exec `shouldBe` []
        it "should have `unit` as it_const" $ do
          m_it_consts unit_exec `shouldBe` [ConstantData (mk_name ["unit"]) []]
        it "should use dependent elimination" $ do
          m_dep_elim unit_exec `shouldBe` True
        it "should elim to any Type" $ do
          m_elim_level unit_exec `shouldBe` (Just (mk_level_param (mk_system_name_s "elim_level")))
        it "should simplify unit.rec" $ do
          case tc_run (m_env unit_exec) [] 0 (TypeChecker.whnf unit_rec_example) of
            Right e -> e `shouldBe` star_const


nat_spec = 
  let nat_name = mk_name ["nat"]
      nat_const = mk_constant nat_name []
      nat_type = mk_Type
      zero_type = nat_const
      zero_name = mk_name ["zero","nat"]
      zero_const = mk_constant zero_name []
      succ_type = mk_pi_anon nat_const nat_const
      succ_name = mk_name ["succ","nat"]
      succ_const = mk_constant succ_name []
      nat_decls = [InductiveDecl
                   (mk_name ["nat"])
                   nat_type
                   [IntroRule zero_name zero_type,
                    IntroRule succ_name succ_type]]
      nat_exec = ind_exec add_inductive_core empty_environment [] 0 nat_decls
      one = mk_app succ_const zero_const
      two = mk_app succ_const one
      four = mk_app succ_const (mk_app succ_const two)
      c = mk_lambda_anon nat_const nat_const
      c0 = zero_const
      cs = mk_lambda_anon nat_const (mk_lambda_anon nat_const (mk_app succ_const (mk_app succ_const (mk_var 0))))
      rec_const = mk_constant (mk_name ["rec","nat"]) [mk_level_one]
      nrec1 = mk_app_seq rec_const [c,c0,cs,one]
      nrec2 = mk_app_seq rec_const [c,c0,cs,two]      
      new_env = m_env nat_exec
  in do
    describe "Inductive processing of nat" $ do
      it "should support one recursive step" $ do
        err_is_def_eq new_env [] nrec1 two `shouldBe` True
      it "should support two recursive steps" $ do
        err_is_def_eq new_env [] nrec2 four `shouldBe` True

err_is_def_eq env lp_names e1 e2 =
  case tc_run env lp_names 0 (TypeChecker.is_def_eq e1 e2) of
    Right e -> e
    Left err -> error (show err)


{-
list.{l_1} : Type.{l_1} → Type.{max 1 l_1}
list.nil.{l_1} : Π {T : Type.{l_1}}, list.{l_1} T
list.cons.{l_1} : Π {T : Type.{l_1}}, T → list.{l_1} T → list.{l_1} T
list.rec.{l_1 l_2} :
  Π {T : Type.{l_2}} {C : list.{l_2} T → Type.{l_1}},
    C (@list.nil.{l_2} T) →
    (Π (a : T) (a_1 : list.{l_2} T), C a_1 → C (@list.cons.{l_2} T a a_1)) → (Π (n : list.{l_2} T), C n)
-}
list_spec = 
  let list_name = mk_name ["list"]
      list_lp_name = mk_name ["l1"]
      list_lp = mk_level_param list_lp_name
      list_const = mk_constant list_name [list_lp]
      type_l1 = mk_sort list_lp
      list_type = mk_pi_anon type_l1 (mk_sort (mk_max mk_level_one list_lp))
      nil_type = mk_pi_anon type_l1 (mk_app list_const (mk_var 0))
      cons_type = mk_pi_anon type_l1
                  (mk_pi_anon (mk_var 0)
                   (mk_pi_anon (mk_app list_const (mk_var 1)) (mk_app list_const (mk_var 2))))
      list_decls = [InductiveDecl
                    (mk_name ["list"])
                    list_type
                    [IntroRule (mk_name ["nil","list"]) nil_type,
                     IntroRule (mk_name ["cons","list"]) cons_type]]
  in 
    describe "Inductive processing of list " $ do
    let list_result = ind_run add_inductive_core empty_environment [list_lp_name] 1 list_decls
        list_eval = fst list_result
        list_exec = snd list_result        
      in
      describe "check_inductive_types" $ do
        it "should not throw an error" $ do
          list_eval `shouldBe` (Right ())
        it "should be at level (max 1 list_lp)" $ do
          m_it_levels list_exec `shouldBe` [mk_max mk_level_one list_lp]
        it "should have 1 it_num_arg" $ do
          m_it_num_args list_exec `shouldBe` [1]
        it "should have one param_const, Type.{list_lp}" $ do
          local_type ((m_param_consts list_exec)!!0) `shouldBe` type_l1
        it "should have `list` as it_const" $ do
          m_it_consts list_exec `shouldBe` [ConstantData list_name [list_lp]]
        it "should use dependent elimination" $ do
          m_dep_elim list_exec `shouldBe` True
        it "should elim to any Type" $ do
          m_elim_level list_exec `shouldBe` (Just (mk_level_param (mk_system_name_s "elim_level")))
{-        it "should have correct comp rule" $ do
          let env = m_env list_exec
              ext = env_ind_ext env
              comp_rules = iext_comp_rules ext in
              comp_rules `shouldBe` Map.empty -- TODO just to print
-}

{-
eq.{l_1} : Π {A : Type.{l_1}}, A → A → Prop
eq.refl.{l_1} : ∀ {A : Type.{l_1}} (a : A), @eq.{l_1} A a a
eq.rec.{l_1 l_2} :
  Π {A : Type.{l_2}} {a : A} {C : A → Type.{l_1}},
    C a → (Π {a_1 : A}, @eq.{l_2} A a a_1 → C a_1)
-}          
eq_spec = 
  let eq_name = mk_name ["eq"]
      eq_lp_name = mk_name ["l1"]
      eq_lp = mk_level_param eq_lp_name
      eq_const = mk_constant eq_name [eq_lp]
      type_l1 = mk_sort eq_lp
      eq_type = mk_pi_anon type_l1 (mk_pi_anon (mk_var 0) (mk_pi_anon (mk_var 1) mk_Prop))
      refl_type = mk_pi_anon type_l1 (mk_pi_anon (mk_var 0) (mk_app_seq eq_const [mk_var 1, mk_var 0, mk_var 0]))
      eq_decls = [InductiveDecl
                    eq_name
                    eq_type
                    [IntroRule (mk_name ["refl","eq"]) refl_type]]
  in 
    describe "Inductive processing of eq " $ do
    let eq_result = ind_run add_inductive_core empty_environment [eq_lp_name] 2 eq_decls
        eq_eval = fst eq_result
        eq_exec = snd eq_result        
      in
      describe "check_inductive_types" $ do
        it "should not throw an error" $ do
          eq_eval `shouldBe` (Right ())
        it "should be at level zero" $ do
          m_it_levels eq_exec `shouldBe` [mk_zero]
        it "should have 3 it_num_arg" $ do
          m_it_num_args eq_exec `shouldBe` [3]
        it "should have 2 param_const, Type.{l1} and something of that type" $ do
          -- TODO '3' is not stable
          map local_type (m_param_consts eq_exec) `shouldBe` [type_l1, Local $ mk_local_data (mk_system_name_i 3) no_name type_l1]
        it "should have `eq` as it_const" $ do
          m_it_consts eq_exec `shouldBe` [ConstantData eq_name [eq_lp]]
        -- TODO why not
        it "should not use dependent elimination" $ do
          m_dep_elim eq_exec `shouldBe` False
        it "should elim to any Type" $ do
          m_elim_level eq_exec `shouldBe` (Just (mk_level_param (mk_system_name_s "elim_level")))

check_no_inductive_type_decls = do
  describe "NoInductiveTypeDecls" $ 
    it "should trigger exception" $ do
      (ind_eval add_inductive_core empty_environment [] 0 []) `shouldBe` (Left NoInductiveTypeDecls)

exceptions_spec :: Spec
exceptions_spec =
  describe "InductiveDeclError" $ do
    check_no_inductive_type_decls

{-
  data InductiveDeclError = NoInductiveTypeDecls
                        | ParamsOfInductiveTypesMustMatch
                        | NumParamsMismatchInInductiveDecl Integer Integer
                        | ArgDoesNotMatchInductiveParameters Integer Name
                        | UniLevelOfArgTooBig Integer Name
                        | OneInPropAllInProp 
                        | NonRecArgAfterRecArg Integer Name
                        | InvalidRecArg Integer Name
                        | InvalidReturnType Name
                        | NonPosOccurrence Integer Name
                        | NonValidOccurrence Integer Name
                        | TypeCheckError TypeChecker.TypeError
                        deriving (Eq,Show)
-}

spec :: Spec
spec = do
  unit_spec
  nat_spec
  list_spec
  eq_spec
  exceptions_spec
