module Main where

import System.Environment
import Parser

import Name
import Level
import Expression
import Environment
import qualified TypeChecker as TypeChecker
import qualified Inductive as Inductive

import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Except

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import Data.List (findIndex)
import Debug.Trace

data ExportRepeatError = RepeatedName | RepeatedLevel | RepeatedExpression | RepeatedUNI deriving (Show)

data KernelError = ExportError ExportRepeatError
                 | TypeError TypeChecker.TypeError
                 | InductiveDeclError Inductive.InductiveDeclError deriving (Show)

data Context = Context {
  name_map :: Map Integer Name,
  level_map :: Map Integer Level,
  expr_map :: Map Integer Expression,
  global_env :: Environment,
  def_id :: Integer,
  ind_id :: Integer
  }


initial_context = Context (Map.insert 0 Anonymous Map.empty) (Map.insert 0 mk_level_zero Map.empty) Map.empty empty_environment 0 0

interpret :: [Statement] -> ExceptT KernelError (State Context) Environment
interpret [] = gets global_env
interpret (statement:statements) = interpret_statement statement >> interpret statements

assert_undefined n_idx m err = if Map.member n_idx m then throwE (ExportError err) else return ()

interpret_statement statement =
  case statement of
    StatementNI n_idx o_idx i -> do m <- gets name_map
                                    assert_undefined n_idx m RepeatedName
                                    modify (\c -> c { name_map = Map.insert n_idx (AppendInteger (m Map.! o_idx) i) m } )
    StatementNS n_idx o_idx s -> do m <- gets name_map
                                    assert_undefined n_idx m RepeatedName
                                    modify (\c -> c { name_map = Map.insert n_idx (AppendString (m Map.! o_idx) s) m } )

    StatementUS n_idx o_idx -> do m <- gets level_map
                                  assert_undefined n_idx m RepeatedLevel
                                  modify (\c -> c { level_map = Map.insert n_idx (mk_succ (m Map.! o_idx)) m })

    StatementUM n_idx o_idx1 o_idx2 -> do m <- gets level_map
                                          assert_undefined n_idx m RepeatedLevel
                                          modify (\c -> c { level_map = Map.insert n_idx (mk_max (m Map.! o_idx1) (m Map.! o_idx2)) m })

    StatementUIM n_idx o_idx1 o_idx2 -> do m <- gets level_map
                                           assert_undefined n_idx m RepeatedLevel
                                           modify (\c -> c { level_map = Map.insert n_idx (mk_imax (m Map.! o_idx1) (m Map.! o_idx2)) m })

    StatementUP n_idx o_idx -> do m <- gets level_map
                                  mn <- gets name_map
                                  assert_undefined n_idx m RepeatedLevel
                                  modify (\c -> c { level_map = Map.insert n_idx (mk_level_param (mn Map.! o_idx)) m })

    StatementUG n_idx o_idx -> do m <- gets level_map
                                  mn <- gets name_map
                                  assert_undefined n_idx m RepeatedLevel
                                  modify (\c -> c { level_map = Map.insert n_idx (mk_global_univ (mn Map.! o_idx)) m })

    StatementEV n_idx v -> do m <- gets expr_map
                              assert_undefined n_idx m RepeatedExpression
                              modify (\c -> c { expr_map = Map.insert n_idx (mk_var v) m })

    StatementES n_idx o_idx -> do m <- gets expr_map
                                  ml <- gets level_map
                                  assert_undefined n_idx m RepeatedExpression
                                  modify(\c -> c { expr_map = Map.insert n_idx (mk_sort (ml Map.! o_idx)) m })

    StatementEC n_idx o_idx l_idxs -> do m <- gets expr_map
                                         mn <- gets name_map
                                         ml <- gets level_map
                                         assert_undefined n_idx m RepeatedExpression
                                         modify (\c -> c { expr_map = Map.insert n_idx (mk_constant (mn Map.! o_idx)
                                                                                        (map (ml Map.!) l_idxs)) m })

    StatementEA n_idx o_idx1 o_idx2 -> do m <- gets expr_map
                                          assert_undefined n_idx m RepeatedExpression
                                          modify (\c -> c { expr_map = Map.insert n_idx (mk_app (m Map.! o_idx1) (m Map.! o_idx2)) m })

    StatementEL n_idx b_info name_idx domain_idx body_idx ->
      do m <- gets expr_map
         mn <- gets name_map
         assert_undefined n_idx m RepeatedExpression
         modify (\c -> c { expr_map = Map.insert n_idx (mk_lambda (mn Map.! name_idx)
                                                        (m Map.! domain_idx)
                                                        (m Map.! body_idx)
                                                        b_info) m })

    StatementEP n_idx b_info name_idx domain_idx body_idx ->
      do m <- gets expr_map
         mn <- gets name_map
         assert_undefined n_idx m RepeatedExpression
         modify (\c -> c { expr_map = Map.insert n_idx (mk_pi (mn Map.! name_idx)
                                                        (m Map.! domain_idx)
                                                        (m Map.! body_idx)
                                                        b_info) m })

    StatementBIND num_params _ level_name_idxs idecls ->
      do me <- gets expr_map
         mn <- gets name_map
         did <- gets ind_id
         modify (\s -> s { ind_id = did + 1 })
         let level_names = map (mn Map.!) level_name_idxs
             inductive_decls = map (instantiate_idecl mn me) idecls in do
           trace ("BIND(" ++ show did ++ "): " ++ (show (map (\(InductiveDecl name _ _) -> name) inductive_decls))) (return ())
           old_env <- gets global_env
           new_env <- register_inductive old_env level_names num_params inductive_decls
           modify (\c -> c { global_env = new_env })

    StatementUNI name_idx -> do mn <- gets name_map
                                old_env <- gets global_env
                                let name = mn Map.! name_idx in
                                  if Set.member name (env_global_names old_env)
                                  then throwE . ExportError $ RepeatedUNI
                                  else modify (\c -> c { global_env = env_add_uni old_env name })
                                    
    StatementDEF name_idx level_name_idxs type_idx value_idx ->
      do mn <- gets name_map
         me <- gets expr_map
         old_env <- gets global_env
         did <- gets def_id
         modify (\s -> s { def_id = did + 1 })         
         let name = mn Map.! name_idx
             level_names = map (mn Map.!) level_name_idxs
             def_type = me Map.! type_idx
             def_value = me Map.! value_idx
             decl = mk_definition old_env name level_names def_type def_value in do
           trace ("DEF(" ++ show did ++ "): " ++ show name) (return ())
           case TypeChecker.check old_env decl of
             Left err -> throwE $ TypeError err
             Right cdecl -> modify (\c -> c { global_env = env_add old_env cdecl })
           
    StatementAX name_idx level_name_idxs type_idx ->
      do mn <- gets name_map
         me <- gets expr_map
         old_env <- gets global_env
         let name = mn Map.! name_idx
             level_names = map (mn Map.!) level_name_idxs
             ax_type = me Map.! type_idx
             decl = mk_axiom name level_names ax_type in
           case TypeChecker.check old_env decl of
             Left err -> throwE $ TypeError err
             Right cdecl -> modify (\c -> c { global_env = env_add old_env cdecl })

instantiate_idecl mn me (IDecl n_idx e_idx irs) =
  let ind_name = mn Map.! n_idx
      ind_type = me Map.! e_idx
      intro_rules = map instantiate_intro_rule irs in
  InductiveDecl ind_name ind_type intro_rules
  where
    instantiate_intro_rule (IIntro n_idx e_idx) = IntroRule (mn Map.! n_idx) (me Map.! e_idx)

register_inductive env level_param_names num_params idecls =
  case Inductive.add_inductive env level_param_names num_params idecls of
    Left err -> throwE $ InductiveDeclError err
    Right env -> return env

    

isBIND x = case words x of
  ("#BIND" : _) -> True
  _ -> False

isEIND x = case words x of
  ("#EIND" : _) -> True
  _ -> False

splitAtStatements s = splitLines (lines s) where
  splitLines [] = []
  splitLines (x:xs)
    | isBIND x = case findIndex isEIND xs of
      Just k -> (unlines $ x : (take (k+1) xs)) : splitLines (drop (k+1) xs)
    | otherwise = x : splitLines xs

main = do
  args <- getArgs
  content <- readFile (args !! 0)
--  print $ splitAtStatements content
  print $ case evalState (runExceptT $ interpret . (map (parseStatement . lexStatement)) . splitAtStatements $ content) initial_context of
    Left err -> show err
    Right _ -> "Congratulations!"




