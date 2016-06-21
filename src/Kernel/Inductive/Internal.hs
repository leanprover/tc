{-|
Module      : Kernel.Inductive.Internal
Description : Inductive type declarations
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Implementation of inductive type declaration processing.
The main roles of this module are:
1. To validate inductive type declarations
2. To compute the corresponding eliminator
3. To compute the corresponding computation rule
-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module Kernel.Inductive.Internal where

import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe

import Kernel.Name
import Kernel.Level
import Kernel.Expr
import Kernel.TypeChecker (IndDecl(IndDecl)
                          , indDeclNumParams, indDeclLPNames, indDeclName, indDeclType, indDeclIntroRules
                          , IntroRule(IntroRule)
                          , CompRule(CompRule)
                          , Env
                          , envPropProofIrrel, envPropImpredicative
                          , envAddIndDecl, envAddIntroRule, envAddElimInfo, envAddCompRule, envLookupDecl
                          , TypeError, TCMethod)

import qualified Kernel.TypeChecker as TypeChecker

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import Lens.Simple (Lens, lens, makeLenses, use, uses, view, over, (%=), (.=), (%%=))

import Data.List (genericIndex,genericLength,genericTake,genericDrop,genericSplitAt)
import qualified Data.Maybe as Maybe

type Eventually = Maybe

-- (Unsafe) Maybe lenses. Note that
_Elem :: Lens (Eventually a) (Eventually b) a b
_Elem = lens Maybe.fromJust (\ma b' -> Just b')

data IndDeclError = NumParamsMismatchInIndDecl Int Int
                        | ArgDoesNotMatchInductiveParameters Int Name
                        | UniLevelOfArgTooBig Int Name Level Level
                        | NonRecArgAfterRecArg Int Name
                        | InvalidRecArg Int Name
                        | InvalidReturnType Name
                        | NonPosOccurrence Int Name
                        | NonValidOccurrence Int Name
                        | TypeCheckError TypeChecker.TypeError String
                        deriving (Eq,Show)

data ElimInfo = ElimInfo {
  _elimInfoC :: LocalData, -- type former constant
  _elimInfoIndices :: [LocalData], --local constant for each index
  _elimInfoMajorPremise :: LocalData, -- major premise for each inductive decl
  _elimInfoMinorPremises :: [LocalData] -- minor premise for each introduction rule
} deriving (Eq,Show)

makeLenses ''ElimInfo

data AddInductiveS = AddInductiveS {
  _addIndEnv :: Env,
  _addIndIDecl :: IndDecl,

  _addIndIsDefinitelyNotZero :: Bool,
  _addIndNextId :: Integer,
  _addIndDepElim :: Bool,

  _addIndElimLevel :: Eventually Level,
  _addIndParamLocals :: Eventually [LocalData], -- local constants used to represent global parameters
  _addIndIndIndexLocals :: Eventually [LocalData], -- local constants used to represent indices
  _addIndIndBody :: Eventually Expr, -- inner body of indType
  _addIndIndLevel :: Eventually Level, -- the levels for each inductive datatype in [m_idecls]
  _addIndIndConst :: Eventually ConstantData, -- the constants for each inductive datatype in [m_idecls]
  _addIndNumArgs :: Eventually Int, -- total number of arguments (params + indices) for each inductive datatype in m_idecls

  _addIndElimInfo :: Eventually ElimInfo,
  _addIndKTarget :: Bool
}

makeLenses ''AddInductiveS

mkAddInductiveS :: Env -> IndDecl -> AddInductiveS
mkAddInductiveS env idecl = AddInductiveS {
  _addIndEnv = env,
  _addIndIDecl = idecl,

  _addIndNextId = 0,

  _addIndIsDefinitelyNotZero = False,
  _addIndDepElim = False,
  _addIndElimLevel = Nothing,

  _addIndParamLocals = Nothing,
  _addIndIndIndexLocals = Nothing,
  _addIndIndBody = Nothing,
  _addIndIndLevel = Nothing,
  _addIndIndConst = Nothing,
  _addIndNumArgs = Nothing,
  _addIndElimInfo = Nothing,
  _addIndKTarget = False
  }

type AddInductiveMethod = ExceptT IndDeclError (State AddInductiveS)

{- Misc -}

gensym :: AddInductiveMethod Integer
gensym = addIndNextId %%= \n -> (n, n + 1)

mkLocalFor :: BindingData -> AddInductiveMethod LocalData
mkLocalFor bind = do
  nextId <- gensym
  return $ mkLocalData (mkSystemNameI nextId) (bindingName bind) (bindingDomain bind) (bindingInfo bind)

indAssert :: IndDeclError -> Bool -> AddInductiveMethod ()
indAssert err b = if b then return () else throwE err

-- TODO(dhs): why did old version add another layer to this?
mkFreshName :: AddInductiveMethod Name
mkFreshName = gensym >>= return . mkSystemNameI

addInductive :: Env -> IndDecl -> Either IndDeclError Env
addInductive env idecl =
  let (a, s) = runState (runExceptT addInductiveCore) (mkAddInductiveS env idecl) in
   case a of
    Left err -> Left err
    Right () -> Right $ view addIndEnv s

addInductiveCore :: AddInductiveMethod ()
addInductiveCore = do
  checkIndType
  declareIndType
  checkIntroRules
  declareIntroRules
  computeElimRule
  declareElimRule
  mkCompRules

checkIndType :: AddInductiveMethod ()
checkIndType = do
  (IndDecl numParams lpNames name ty introRules) <- use addIndIDecl
  checkType ty lpNames
  -- The first [numParams] arguments represent the "parameters"
  (paramLocals, rest) <- telescopePiN numParams ty
  indAssert (NumParamsMismatchInIndDecl (length paramLocals) numParams) (length paramLocals == numParams)
  -- The remaining arguments represent the "indices"
  (indIndexLocals, body) <- telescopePi rest
  -- The inner body must be a Sort
  sort <- ensureSort body lpNames
  lpNames <- uses addIndIDecl (map mkLevelParam . view indDeclLPNames)
  addIndIsDefinitelyNotZero .= isDefinitelyNotZero (sortLevel sort)
  addIndIndConst .= Just (ConstantData name lpNames)
  addIndIndLevel .= Just (sortLevel sort)
  addIndNumArgs .= Just (numParams + length indIndexLocals)
  addIndParamLocals .= Just paramLocals
  addIndIndIndexLocals .= Just indIndexLocals
  addIndIndBody .= Just body
      where
        telescopePiN :: Int -> Expr -> AddInductiveMethod ([LocalData], Expr)
        telescopePiN numTake e = telescopePiNCore numTake [] e

        telescopePiNCore :: Int -> [LocalData] -> Expr -> AddInductiveMethod ([LocalData], Expr)
        telescopePiNCore numTake locals e =
          case e of
            _ | numTake <= 0 -> return (locals, e)
            Pi pi -> do local <- mkLocalFor pi
                        telescopePiNCore (numTake - 1) (locals ++ [local]) (instantiate (bindingBody pi) (Local local))
            _ -> return (locals, e)

        telescopePi :: Expr -> AddInductiveMethod ([LocalData], Expr)
        telescopePi e = telescopePiCore [] e

        telescopePiCore :: [LocalData] -> Expr -> AddInductiveMethod ([LocalData], Expr)
        telescopePiCore locals e =
            case e of
              Pi pi -> do local <- mkLocalFor pi
                          telescopePiCore (locals ++ [local]) (instantiate (bindingBody pi) (Local local))
              _ -> return (locals, e)


-- Add all datatype declarations to environment.
declareIndType :: AddInductiveMethod ()
declareIndType = do
  idecl@(IndDecl numParams lpNames name ty introRules) <- use addIndIDecl
  envAddAxiom name lpNames ty
  addIndEnv %= envAddIndDecl idecl

{- Check if
   - all introduction rules start with the same parameters
   - the type of all arguments (which are not datatype global params) live in universes <= level of the corresponding datatype
   - all inductive datatype occurrences are positive
   - all introduction rules are well typed

   Note: this method must be executed after declareIndType
-}
checkIntroRules :: AddInductiveMethod ()
checkIntroRules = do
  (IndDecl numParams lpNames name ty introRules) <- use addIndIDecl
  mapM_ (checkIntroRule lpNames) introRules
    where
      checkIntroRule :: [Name] -> IntroRule -> AddInductiveMethod ()
      checkIntroRule lpNames (IntroRule name ty) = do
        checkType ty lpNames
        checkIntroRuleCore 0 False name ty

      checkIntroRuleCore :: Int -> Bool -> Name -> Expr -> AddInductiveMethod ()
      checkIntroRuleCore paramNum foundRec name ty =
        case ty of
         Pi pi -> do
           numParams <- use (addIndIDecl . indDeclNumParams)
           lpNames <- use (addIndIDecl . indDeclLPNames)
           paramLocals <- use (addIndParamLocals . _Elem)
           if paramNum < numParams
             then -- We instantiate the first [numParams] arguments with the *shared* parameters
                do let local = paramLocals !! paramNum
                   isDefEq (bindingDomain pi) (localType local) lpNames >>=
                           indAssert (ArgDoesNotMatchInductiveParameters paramNum name)
                   checkIntroRuleCore (paramNum+1) foundRec name (instantiate (bindingBody pi) (Local local))
             else -- The remaining arguments are unique to this introduction rule
                do sort <- ensureType (bindingDomain pi) lpNames
                   indLevel <- use (addIndIndLevel . _Elem)
                   env <- use addIndEnv
                   -- The universe level of each argument must not exceed that of the inductive type itself
                   indAssert (UniLevelOfArgTooBig paramNum name (sortLevel sort) indLevel)
                                 (levelNotBiggerThan (sortLevel sort) indLevel || (isZero indLevel && view envPropImpredicative env))
                   domainTy <- whnf (bindingDomain pi)
                   -- All occurrences of the inductive type itself must be "positive"
                   checkPositivity domainTy name paramNum
                   argIsRec <- isRecArg domainTy
                   -- All recursive args must occur after all non-recursive args
                   indAssert (NonRecArgAfterRecArg paramNum name) (not foundRec || argIsRec)
                   ty <- if argIsRec
                         then indAssert (InvalidRecArg paramNum name) (closed (bindingBody pi)) >> return (bindingBody pi)
                         else mkLocalFor pi >>= return . instantiate (bindingBody pi) . Local
                   checkIntroRuleCore (paramNum+1) argIsRec name ty
         _ -> isValidIndApp ty >>= indAssert (InvalidReturnType name) -- add to [irIndices]?

      checkPositivity :: Expr -> Name -> Int -> AddInductiveMethod ()
      checkPositivity ty name paramNum = do
        ty <- whnf ty
        itOccurs <- indTypeOccurs ty
        if not itOccurs then return () else
          case ty of
           Pi pi -> do indTypeOccurs (bindingDomain pi) >>= indAssert (NonPosOccurrence paramNum name) . not
                       local <- mkLocalFor pi
                       checkPositivity (instantiate (bindingBody pi) $ Local local) name paramNum
           _ -> isValidIndApp ty >>= indAssert (NonValidOccurrence paramNum name)

      indTypeOccurs :: Expr -> AddInductiveMethod Bool
      indTypeOccurs e = do
        indTypeConst <- use (addIndIndConst . _Elem)
        return . Maybe.isJust $ findInExpr (\e _ -> case e of
                                             Constant const -> constName const == constName indTypeConst
                                             _ -> False) e

isValidIndApp :: Expr -> AddInductiveMethod Bool
isValidIndApp e = do
  indTypeConst <- use (addIndIndConst . _Elem)
  paramLocals <- use (addIndParamLocals . _Elem)
  lpNames <- use (addIndIDecl . indDeclLPNames)
  numParams <- use (addIndIDecl . indDeclNumParams)
  numArgs <- use (addIndNumArgs . _Elem)
  let (op, args) = getAppOpArgs e
  opEq <- isDefEq op (Constant indTypeConst) lpNames
  return $ opEq && length args == numArgs && all (uncurry (==)) (zip (take numParams args) (map Local paramLocals))

isRecArg :: Expr -> AddInductiveMethod Bool
isRecArg e = do
  e <- whnf e
  case e of
    Pi pi -> mkLocalFor pi >>= isRecArg . (instantiate (bindingBody pi)) . Local
    _ -> isValidIndApp e

declareIntroRules :: AddInductiveMethod ()
declareIntroRules = do
  (IndDecl _ lpNames indName _ introRules) <- use addIndIDecl
  mapM_ (\(IntroRule irName irType) -> do envAddAxiom irName lpNames irType
                                          addIndEnv %= envAddIntroRule irName indName) introRules

computeElimRule :: AddInductiveMethod ()
computeElimRule = do
  initDepElim
  initElimLevel
  initCIndicesMajor
  initMinorPremises
  where
    initDepElim :: AddInductiveMethod ()
    initDepElim = do
      env <- use addIndEnv
      indLevel <- use (addIndIndLevel . _Elem)
      addIndDepElim .= not (view envPropImpredicative env && view envPropProofIrrel env && isZero indLevel)

    initElimLevel :: AddInductiveMethod ()
    initElimLevel = do
      onlyAtZero <- elimOnlyAtLevelZero
      if onlyAtZero
        then addIndElimLevel .= Just mkZero
        else addIndElimLevel .= Just (mkLevelParam (mkSystemNameS "elimLevel"))

    -- Return true if type formers C in the recursors can only map to Type.{0}
    elimOnlyAtLevelZero :: AddInductiveMethod Bool
    elimOnlyAtLevelZero = do
      env <- use addIndEnv
      isDefinitelyNotZero <- use addIndIsDefinitelyNotZero
      if not (view envPropImpredicative env) || isDefinitelyNotZero then return False else do
        (IndDecl _ _ _ _ introRules) <- use addIndIDecl
        case introRules of
         [] -> return False
         (_:_:_) -> return True
         [IntroRule irName irType] -> do
         {- We have only one introduction rule, the final check is, the type of each argument that is not a parameter:
          1- It must live in Type.{0}, *OR*
          2- It must occur in the return type. (this is essentially what is called a non-uniform parameter in Coq).
             We can justify 2 by observing that this information is not a *secret* it is part of the type.
             By eliminating to a non-proposition, we would not be revealing anything that is not already known. -}
           (irBodyType, argsToCheck) <- collectArgsToCheck irType 0
           let resultArgs = getAppArgs irBodyType
           let results = map (not . flip elem resultArgs) $ map Local argsToCheck
           return $ any (==True) results

    {- We proceed through the arguments to the introRule,
       and return (innerBody, [locals for all (non-param) args that do not live in Prop]) -}
    collectArgsToCheck :: Expr -> Int -> AddInductiveMethod (Expr, [LocalData])
    collectArgsToCheck ty paramNum =
      case ty of
        Pi pi -> do local <- mkLocalFor pi
                    let body = instantiate (bindingBody pi) (Local local)
                    (ty, rest) <- collectArgsToCheck body (paramNum+1)
                    numParams <- use (addIndIDecl . indDeclNumParams)
                    lpNames <- use (addIndIDecl . indDeclLPNames)
                    if paramNum >= numParams
                    then do sort <- ensureType (bindingDomain pi) lpNames
                            return $ if not (isZero (sortLevel sort)) then (ty, local : rest) else (ty, rest)
                    else return (ty, rest)
        _ -> return (ty, [])

    initCIndicesMajor :: AddInductiveMethod ()
    initCIndicesMajor = do (IndDecl _ _ indName indType introRules) <- use addIndIDecl
                           paramLocals <- use $ addIndParamLocals . _Elem
                           indIndexLocals <- use $ addIndIndIndexLocals . _Elem
                           indBody <-use $ addIndIndBody . _Elem
                           indConst <- use $ addIndIndConst . _Elem
                           majorName <- mkFreshName
                           let majorPremise = mkLocalData majorName (mkName ["major"])
                                              (mkAppSeq (mkAppSeq (Constant indConst) (map Local paramLocals))
                                                            (map Local indIndexLocals))
                                              BinderDefault
                           elimLevel <- use $ addIndElimLevel . _Elem
                           depElim <- use addIndDepElim
                           let cType0 = mkSort elimLevel
                           let cType1 = if depElim then abstractPi majorPremise cType0 else cType0
                           let cType2 = abstractPiSeq indIndexLocals cType1
                           let cPPName = mkName ["C"]
                           cName <- mkFreshName
                           let c = mkLocalData cName cPPName cType2 BinderDefault
                           addIndElimInfo .= (Just $ ElimInfo c indIndexLocals majorPremise [])

    initMinorPremises :: AddInductiveMethod()
    initMinorPremises =
        do
          (IndDecl _ _ indName indType introRules) <- use addIndIDecl
          env <- use addIndEnv
          indLevel <- use $ addIndIndLevel . _Elem
          -- Note: this is not the final K-Target check
          addIndKTarget .= (view envPropProofIrrel env && isZero indLevel && length introRules == 1)
          mapM_ initMinorPremise introRules

    initMinorPremise :: IntroRule -> AddInductiveMethod ()
    initMinorPremise (IntroRule irName irType) =
        do
          paramLocals <- use $ addIndParamLocals . _Elem
          elimInfo <- use $ addIndElimInfo . _Elem
          depElim <- use addIndDepElim
          indLevel <- use $ addIndIndLevel . _Elem
          levels <- uses (addIndIDecl . indDeclLPNames) (map mkLevelParam)
          (nonRecArgs, recArgs, irBody) <- splitIntroRuleType irType
          irIndices <- getIndices irBody
          c <- use (addIndElimInfo . _Elem . elimInfoC)
          indArgs <- constructIndArgs recArgs [0..]
          minorPremiseName <- mkFreshName
          let minorPremiseType0 = mkAppSeq (Local c) irIndices
          let minorPremiseType1 = if depElim
                                  then let introApp = mkAppSeq
                                                      (mkAppSeq
                                                       (mkAppSeq (mkConstant irName levels)
                                                                     (map Local paramLocals))
                                                       (map Local nonRecArgs))
                                                      (map Local recArgs) in
                                       mkApp minorPremiseType0 introApp
                                  else minorPremiseType0
          let minorPremiseType2 = abstractPiSeq nonRecArgs
                                  (abstractPiSeq recArgs
                                   (abstractPiSeq indArgs minorPremiseType1))
          let minorPremise = mkLocalData minorPremiseName (mkName ["e"]) minorPremiseType2 BinderDefault
          (addIndElimInfo . _Elem . elimInfoMinorPremises) %= (++ [minorPremise])

splitIntroRuleType :: Expr -> AddInductiveMethod ([LocalData], [LocalData], Expr)
splitIntroRuleType irType = splitIntroRuleTypeCore [] [] irType 0
    where
      splitIntroRuleTypeCore :: [LocalData] -> [LocalData] -> Expr -> Int -> AddInductiveMethod ([LocalData], [LocalData], Expr)
      splitIntroRuleTypeCore nonRecArgs recArgs irType paramNum =
          do
            numParams <- use (addIndIDecl . indDeclNumParams)
            case irType of
              Pi pi | paramNum < numParams -> do
                          paramLocal <- uses (addIndParamLocals . _Elem) (!! paramNum)
                          splitIntroRuleTypeCore nonRecArgs recArgs (instantiate (bindingBody pi) (Local paramLocal)) (paramNum+1)
                    | otherwise ->
                        do
                          -- intro rule has an argument, so we set KTarget to False
                          addIndKTarget .= False
                          local <- mkLocalFor pi
                          argIsRec <- isRecArg (bindingDomain pi)
                          let (newNonRecArgs, newRecArgs) = if argIsRec then (nonRecArgs, recArgs ++ [local]) else (nonRecArgs ++ [local], recArgs)
                          splitIntroRuleTypeCore newNonRecArgs newRecArgs (instantiate (bindingBody pi) (Local local)) (paramNum+1)
              _ -> return (nonRecArgs, recArgs, irType)

constructIndArgs :: [LocalData] -> [Int] -> AddInductiveMethod [LocalData]
constructIndArgs [] _ = return []
constructIndArgs (recArg : recArgs) (recArgNum : recArgNums) =
    do
      restIndArgs <- constructIndArgs recArgs recArgNums
      recArgType <- whnf (localType recArg)
      (xs, recArgBody) <- constructIndArgArgs recArgType
      c <- use (addIndElimInfo . _Elem . elimInfoC)
      recArgIndices <- getIndices recArgBody
      let cApp0 = mkAppSeq (Local c) recArgIndices
      depElim <- use addIndDepElim
      let cApp1 = if depElim
                  then mkApp cApp0 (mkAppSeq (Local recArg) (map Local xs))
                  else cApp0
      let indArgType = abstractPiSeq xs cApp1
      indArgName <- mkFreshName
      let indArg = mkLocalData indArgName (nameRConsI (mkName ["v"]) $ toInteger recArgNum) indArgType BinderDefault
      return $ indArg : restIndArgs

constructIndArgArgs :: Expr -> AddInductiveMethod ([LocalData], Expr)
constructIndArgArgs recArgType = constructIndArgArgsCore [] recArgType
    where
      constructIndArgArgsCore :: [LocalData] -> Expr -> AddInductiveMethod ([LocalData], Expr)
      constructIndArgArgsCore xs recArgType =
          case recArgType of
            Pi pi -> do local <- mkLocalFor pi
                        constructIndArgArgsCore (xs ++ [local]) (instantiate (bindingBody pi) (Local local))
            _ -> return (xs, recArgType)

getIndices :: Expr -> AddInductiveMethod [Expr]
getIndices e = do
  e_n <- whnf e
  isValid <- isValidIndApp e_n
  case isValid of
    True -> do
      numParams <- use (addIndIDecl . indDeclNumParams)
      return $ drop numParams (getAppArgs e_n)

declareElimRule :: AddInductiveMethod ()
declareElimRule =
  do
    (IndDecl numParams lpNames indName indType introRules) <- use addIndIDecl
    elimInfo <- use (addIndElimInfo . _Elem)
    let c = view elimInfoC elimInfo
    let majorPremise = view elimInfoMajorPremise elimInfo
    let minorPremises = view elimInfoMinorPremises elimInfo
    kTarget <- use addIndKTarget
    paramLocals <- use (addIndParamLocals . _Elem)
    indIndexLocals <- use (addIndIndIndexLocals . _Elem)
    depElim <- use addIndDepElim
    elimLPNames <- getElimLPNames
    let elimType0 = mkAppSeq (Local c) (map Local indIndexLocals)
    let elimType1 = if depElim then mkApp elimType0 (Local majorPremise) else elimType0
    let elimType2 = abstractPi majorPremise elimType1
    let elimType3 = abstractPiSeq indIndexLocals elimType2
    let elimType4 = foldr abstractPi elimType3 minorPremises
    let elimType5 = abstractPi c elimType4
    let elimType6 = abstractPiSeq paramLocals elimType5
    envAddAxiom (getElimName indName) elimLPNames elimType6
    let tcElimInfo = TypeChecker.ElimInfo indName elimLPNames numParams (numParams + 1 + length introRules)
                                          (length indIndexLocals) kTarget depElim
    addIndEnv %= envAddElimInfo (getElimName indName) tcElimInfo

getElimName :: Name -> Name
getElimName indName = nameRConsS indName "rec"

getElimLPNames :: AddInductiveMethod [Name]
getElimLPNames = do
  lpNames <- use (addIndIDecl . indDeclLPNames)
  elimLevel <- use (addIndElimLevel . _Elem)
  case maybeParamName elimLevel of
   Just n -> return $ n : lpNames
   Nothing -> return lpNames

mkCompRules :: AddInductiveMethod ()
mkCompRules = do
  (IndDecl _ _ indName _ introRules) <- use addIndIDecl
  (ElimInfo _ _ _ minorPremises) <- use (addIndElimInfo . _Elem)
  mapM_ (uncurry $ mkCompRule indName) (zip introRules minorPremises)

mkCompRule :: Name -> IntroRule -> LocalData -> AddInductiveMethod ()
mkCompRule indName (IntroRule irName irType) minorPremise = do
  elimInfo <- use $ addIndElimInfo . _Elem
  let c = view elimInfoC elimInfo
  let majorPremise = view elimInfoMajorPremise elimInfo
  let minorPremises = view elimInfoMinorPremises elimInfo
  paramLocals <- use (addIndParamLocals . _Elem)
  elimLPNames <- getElimLPNames
  (nonRecArgs, recArgs, _) <- splitIntroRuleType irType
  recApps <- constructRecApps recArgs
  let compRHS0 = mkAppSeq (mkAppSeq (mkAppSeq (Local minorPremise)
                                     (map Local nonRecArgs))
                           (map Local recArgs)) recApps
  let compRHS1 = abstractLambdaSeq paramLocals
                 (abstractLambda c
                  (abstractLambdaSeq minorPremises
                   (abstractLambdaSeq nonRecArgs
                    (abstractLambdaSeq recArgs compRHS0))))
  checkType compRHS1 elimLPNames
  addIndEnv %= envAddCompRule irName (CompRule (getElimName indName) (length nonRecArgs + length recArgs) compRHS1)
    where
      constructRecApps :: [LocalData] -> AddInductiveMethod [Expr]
      constructRecApps [] = return []
      constructRecApps (recArg:recArgs) = do
        elimInfo <- use $ addIndElimInfo . _Elem
        let c = view elimInfoC elimInfo
        let majorPremise = view elimInfoMajorPremise elimInfo
        let minorPremises = view elimInfoMinorPremises elimInfo
        paramLocals <- use (addIndParamLocals . _Elem)
        indIndexLocals <- use (addIndIndIndexLocals . _Elem)
        restApps <- constructRecApps recArgs
        recArgType <- whnf . localType $ recArg
        (xs, recArgBody) <- constructIndArgArgs recArgType
        recArgIndices <- getIndices recArgBody
        let elimName = getElimName indName
        elimLPNames <- map mkLevelParam <$> getElimLPNames
        let recApp0 = mkConstant elimName elimLPNames
        let recApp1 = mkApp (mkAppSeq (mkAppSeq (mkApp (mkAppSeq recApp0 (map Local paramLocals))
                                                           (Local c))
                                       (map Local minorPremises))
                             recArgIndices)
                      (mkAppSeq (Local recArg) (map Local xs))
        let recApp2 = abstractLambdaSeq xs recApp1
        return $ recApp2 : restApps

{- Wrappers for the type checker -}

wrapTC :: Expr -> [Name] -> (Expr -> TCMethod a) -> String -> AddInductiveMethod a
wrapTC e lpNames tcFn msg = do
  env <- use addIndEnv
  nextId <- use addIndNextId
  case TypeChecker.tcEval env lpNames nextId (tcFn e) of
    Left tcErr -> throwE $ TypeCheckError tcErr msg
    Right (val, next) -> addIndNextId .= next >> return val

checkType :: Expr -> [Name] -> AddInductiveMethod Expr
checkType e lpNames = wrapTC e lpNames TypeChecker.inferType "inferType"

ensureSort :: Expr -> [Name] -> AddInductiveMethod SortData
ensureSort e lpNames = wrapTC e lpNames TypeChecker.ensureSort "ensureSort"

ensureType :: Expr -> [Name] -> AddInductiveMethod SortData
ensureType e lpNames = wrapTC e lpNames TypeChecker.ensureType "ensureType"

whnf :: Expr -> AddInductiveMethod Expr
whnf e = wrapTC e [] TypeChecker.whnf "whnf"

isDefEq :: Expr -> Expr -> [Name] -> AddInductiveMethod Bool
isDefEq e1 e2 lpNames = do
  env <- use addIndEnv
  nextId <- use addIndNextId
  case TypeChecker.tcEval env lpNames nextId (TypeChecker.isDefEq e1 e2) of
    Left tcErr -> throwE $ TypeCheckError tcErr "isDefEq"
    Right (b, next) -> addIndNextId .= next >> return b

envAddAxiom :: Name -> [Name] -> Expr -> AddInductiveMethod ()
envAddAxiom name lpNames ty = do
  env <- use addIndEnv
  case TypeChecker.envAddAxiom name lpNames ty env of
    Left tcErr -> throwE $ TypeCheckError tcErr "envAddAxiom"
    Right env -> addIndEnv .= env
