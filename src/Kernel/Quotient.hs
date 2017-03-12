{-|
Module      : Kernel.Quotients
Description : Declare quotient.
Copyright   : (c) Daniel Selsam, 2017
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Declare quotient.
-}
module Kernel.Quotient (QuotientError, declareQuotient) where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe

import Kernel.Name
import Kernel.Level
import Kernel.Expr
import Kernel.TypeChecker (Env, TypeError)

import qualified Kernel.TypeChecker as TypeChecker

data QuotientError = TypeError TypeChecker.TypeError
                     deriving (Eq, Show)

type QuotientMethod = ExceptT QuotientError (State Env)

gQuotient           = mkName ["quot"]
gQuotientLift      = mkName["quot", "lift"]
gQuotientInd       = mkName["quot", "ind"]
gQuotientMk        = mkName ["quot", "mk"]

declareQuotient :: Env -> Either QuotientError Env
declareQuotient env = evalState (runExceptT declareQuotientCore) env

checkEqType :: QuotientMethod ()
checkEqType = return () -- TODO(dhs): check

addConstant :: Name -> [Name] -> Expr -> QuotientMethod ()
addConstant n lpNames ty = do
  env <- get
  case TypeChecker.envAddAxiom n lpNames ty env of
    Left err -> throwE (TypeError err)
    Right newEnv -> put newEnv

initializeQuotExt :: QuotientMethod ()
initializeQuotExt = do
  env <- get
  put (TypeChecker.initQuotients env)

declareQuotientCore :: QuotientMethod Env
declareQuotientCore = do
  checkEqType
  let uName = mkName ["u"]
  let u = mkLevelParam uName
  let sortU = mkSort u
  let alpha = mkLocalData (mkName ["alpha"]) (mkName ["alpha"]) sortU BinderImplicit
  let r = mkLocalDataDefault (mkName ["r"]) (mkArrow (Local alpha) (mkArrow (Local alpha) mkProp))
  addConstant gQuotient [uName] (abstractPi alpha (abstractPi r sortU))
  let quotR = mkAppSeq (mkConstant gQuotient [u]) [Local alpha, Local r]
  let a = mkLocalDataDefault (mkName ["a"]) (Local alpha)
  addConstant gQuotientMk [uName] (abstractPi alpha (abstractPi r (abstractPi a quotR)))
  let r = mkLocalData (mkName ["r"]) (mkName ["r"]) (mkArrow (Local alpha) (mkArrow (Local alpha) mkProp)) BinderImplicit
  let vName = mkName ["v"]
  let v = mkLevelParam vName
  let sortV = mkSort v
  let beta = mkLocalData (mkName ["beta"]) (mkName ["beta"]) sortV BinderImplicit
  let f = mkLocalDataDefault (mkName ["f"]) (mkArrow (Local alpha) (Local beta))
  let b = mkLocalDataDefault (mkName ["b"]) (Local alpha)
  let r_a_b = mkAppSeq (Local r) [Local a, Local b]
  let f_a_eq_f_b = mkAppSeq (mkConstant (mkName ["eq"]) [v]) [Local beta, mkApp (Local f) (Local a), mkApp (Local f) (Local b)]
  let sanity = abstractPi a (abstractPi b (mkArrow r_a_b f_a_eq_f_b))
  addConstant gQuotientLift [uName, vName]
                  (abstractPi alpha (abstractPi r (abstractPi beta (abstractPi f (mkArrow sanity (mkArrow quotR (Local beta)))))))
  let beta = mkLocalData (mkName ["beta"]) (mkName ["beta"]) (mkArrow quotR mkProp) BinderImplicit
  let quotMk_a = mkAppSeq (mkConstant gQuotientMk [mkLevelParam uName]) [Local alpha, Local r, Local a]
  let allQuot = abstractPi a (mkApp (Local beta) quotMk_a)
  let q = mkLocalDataDefault (mkName ["q"]) quotR
  let beta_q = mkApp (Local beta) (Local q)
  addConstant gQuotientInd [uName]
              (abstractPi alpha (abstractPi r (abstractPi beta (mkArrow allQuot (abstractPi q beta_q)))))
  initializeQuotExt
  get
