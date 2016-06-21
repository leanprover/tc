{-|
Module      : Kernel.TypeChecker
Description : Type checker
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

API for type checker
-}
module Kernel.TypeChecker (
  IndDecl(IndDecl), indDeclNumParams, indDeclLPNames, indDeclName, indDeclType, indDeclIntroRules
  , IntroRule(IntroRule)
  , CompRule(CompRule)
  , ElimInfo(ElimInfo)
  , Env
  , mkStdEnv, mkHottEnv
  , envAddIndDecl, envAddIntroRule, envAddElimInfo, envAddCompRule
  , envHasGlobalLevel, envAddGlobalLevel
  , envLookupDecl
  , envAddAxiom, envAddDefinition
  , envPropProofIrrel, envPropImpredicative
  , TypeError, TCMethod
  , ensureSort, ensureType
  , tcEval, tcRun
  , check, whnf, isDefEq, inferType
  ) where
import Kernel.TypeChecker.Internal
