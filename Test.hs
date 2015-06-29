module Test where

import Name
import Level
import Expression

-- Assert functions
-- TODO these are awful

assertEqual a b = if a == b then return () else do
  putStrLn $ show a ++ "==" ++ show b
  putStrLn $ "assertEqual failed"

assertEqualMsg a b msg = if a == b then return () else do
  putStrLn $ "assertEqual failed: " ++ msg

assertNotEqual a b = if a /= b then return () else do
  putStrLn $ show a ++ "==" ++ show b
  putStrLn $ "assertNotEqual failed"

assert msg b = if b then return () else do
  putStrLn $ "test failed: " ++ msg


-- Levels
  
test_levels =
  let zero = mk_zero
      one = mk_succ zero
      two = mk_succ one
      p1 = mk_level_param (mk_name "p1")
      p2 = mk_level_param (mk_name "p2")      
  in do
    putStrLn "test_levels"
    assertEqual (mk_max one two) two
    assertEqual (mk_imax one two) two
    assertEqual (mk_imax two zero) zero
    assertEqual (mk_imax p1 zero) zero
    assertEqual (mk_max zero p1) p1
    assertEqual (mk_max p1 zero) p1
    assertNotEqual (mk_max p1 one) p1

    assert "max-reduce" $ level_equiv (mk_succ p2) (mk_max p2 (mk_succ p2))
    assert "normalize max" $ level_equiv (mk_max p1 p2) (mk_max p2 p1) 
    assert "not normalize imax" $ not $ level_equiv (mk_imax p1 p2) (mk_imax p2 p1) 
    assert "mk_imax calls mk_max" $ level_equiv (mk_imax (mk_succ p1) (mk_succ p2)) (mk_imax (mk_succ p2) (mk_succ p1)) 
    assert "easy" $ level_equiv one (mk_succ zero)
    assert "easy" $ not $ level_equiv zero two
    assert "easy" $ not $ level_equiv zero p2

-- Expressions
    
mk_dag :: Integer -> Expression
mk_dag depth
  | depth <= 0 = mk_constant (mk_name "a") []
  | otherwise = let a = mk_dag (depth-1) in mk_app (mk_app (mk_constant (mk_name "f") []) a) a

mk_big f depth
  | depth <= 1 = mk_constant (mk_name "foo") []
  | otherwise = let a = mk_big f (depth-1) in mk_app (mk_app f a) a


test_exprs =
  let a = mk_constant (mk_name "a") []
      f = mk_var 0
      fa = mk_app f a
      ty = mk_Type
      lam1 = mk_lambda (mk_name "x") ty (mk_var 0) BinderDefault
      lam2 = mk_lambda (mk_name "y") ty (mk_var 0) BinderDefault
  in do
    putStrLn "test_exprs"
    case fa of App fa_app -> assertEqual (app_fn fa_app) f >> assertEqual (app_arg fa_app) a
    assertEqual (mk_app fa a) (mk_app (mk_app f a) a)
    assertNotEqual (mk_app (mk_app f a) a) (mk_app f (mk_app a a))
    assertEqual (mk_dag 5) (mk_dag 5)
    assertEqual (mk_big (mk_constant (mk_name "f") []) 5) (mk_big (mk_constant (mk_name "f") []) 5)
    

-- Instantiate

test_instantiate = let a = mk_constant (mk_name "a") []
                       b = mk_constant (mk_name "b") []                       
                       r1 = mk_lambda (mk_name "x") mk_Type (mk_app (mk_app (mk_var 0) (mk_var 1)) (mk_var 2)) BinderDefault
                       r2 = mk_lambda (mk_name "x") mk_Type (mk_app (mk_app (mk_var 0) a) (mk_var 1)) BinderDefault
                       r3 = mk_lambda (mk_name "x") mk_Type (mk_app (mk_app (mk_var 0) a) b) BinderDefault                       
                   in do
                    putStrLn "test_instantiate"
                    assertEqual (instantiate r1 a) r2
                    assertEqual (instantiate (instantiate r1 a) b) r3

-- Free vars

-- TODO I need easier ways to create these objects
test_free_vars = let f = mk_constant (mk_name "f") []
                     b = mk_Prop
                     x = mk_local (mk_name "x") (mk_name "x") b BinderDefault
                     y = mk_local (mk_name "y") (mk_name "y") b BinderDefault
                 in case (x,y) of
                   (Local xl, Local yl) -> let
                     s1 = abstract_pi_seq [xl,yl] (mk_app (mk_app f (mk_var 1)) (mk_var 2))
                     s1_l3 = abstract_pi_seq [xl,yl] (mk_app (mk_app f (mk_var 1)) (mk_var 5))
                     t1 = mk_app f (mk_app (abstract_pi_seq [xl,yl] (mk_app (mk_app f x) y)) (mk_app (mk_app f (mk_var 1)) (mk_var 2)))
                     t2 = mk_app t1 x
                     t1_l3 = mk_app f (mk_app (abstract_pi_seq [xl,yl] (mk_app (mk_app f x) y)) (mk_app (mk_app f (mk_var 4)) (mk_var 5)))
                     t2_l3 = mk_app t1_l3 x
                     in do
                       putStrLn "test_free_vars"
                       assertEqual (lift_free_vars s1 3) s1_l3                       
                       assertEqual (lift_free_vars t2 3) t2_l3

main = test_levels >> test_exprs >> test_instantiate >> test_free_vars
