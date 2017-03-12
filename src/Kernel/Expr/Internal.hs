{-|
Module      : Expr
Description : Expressions
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Implementation for expressions
-}
module Kernel.Expr.Internal where

import Kernel.Name
import Kernel.Level

import qualified Data.Maybe as Maybe
import qualified Data.List as List
import Control.Monad (mplus)

data BinderInfo = BinderDefault | BinderImplicit | BinderStrict | BinderClass deriving (Eq,Show,Ord)
data ExprCache = ExprCache { cacheHasLocal :: !Bool,
                             cacheHasLevelParam :: !Bool,
                             cacheFreeVarRange :: !Int } deriving (Eq,Show,Ord)

data VarData = VarData { varIdx :: !Int } deriving (Eq,Show,Ord)

data LocalData = LocalData { localName :: !Name ,
                             localPPName :: !Name,
                             localType :: Expr,
                             localInfo :: !BinderInfo,
                             localCache :: !ExprCache } deriving (Eq,Show,Ord)

data SortData = SortData { sortLevel :: !Level } deriving (Eq,Show,Ord)

data ConstantData = ConstantData { constName :: !Name , constLevels :: ![Level] } deriving (Eq,Show,Ord)

data AppData = AppData { appFn :: Expr, appArg :: Expr, appCache :: !ExprCache  } deriving (Eq,Show,Ord)

data BindingData = BindingData { bindingName :: !Name,
                                 bindingDomain :: Expr,
                                 bindingBody :: Expr,
                                 bindingInfo :: !BinderInfo,
                                 bindingCache :: !ExprCache } deriving (Eq,Show,Ord)

data LetData = LetData { letName :: !Name,
                         letType :: Expr,
                         letVal :: Expr,
                         letBody :: Expr,
                         letCache :: !ExprCache } deriving (Eq,Show,Ord)

data Expr = Var VarData
                | Local !LocalData
                | Sort !SortData
                | Constant !ConstantData
                | Lambda !BindingData
                | Pi !BindingData
                | App !AppData
                | Let !LetData
                deriving (Eq,Ord)

-- TODO(dhs): replace with pretty-printer
showExpression :: Expr -> String
showExpression e = case e of
  Var var -> "#" ++ show (varIdx var)
  Local local -> "(Local <" ++ show (localName local) ++ ">)"
  Sort sort -> if isZero (sortLevel sort) then "Prop" else "Type.{" ++ show (sortLevel sort) ++ "}"
  Constant const -> "'" ++ show (constName const) ++ "'"
  Lambda lam -> "(Lambda: " ++ show (bindingDomain lam) ++ " ==> " ++ show (bindingBody lam) ++ ")"
  Pi pi -> "(Pi: " ++ show (bindingDomain pi) ++ " -> " ++ show (bindingBody pi) ++ ")"
  App app -> let (f,args) = getAppOpArgs e in "(App: " ++ show f ++ " @ " ++ show args ++ ")"
  Let lett -> "(Let: " ++ show (letName lett) ++ " : " ++ showExpression (letType lett) ++ " :=\n" ++ showExpression (letVal lett) ++ "\n in " ++ showExpression (letBody lett) ++ ")"

instance Show Expr where show e = showExpression e

{- Free variables -}

getFreeVarRange :: Expr -> Int
getFreeVarRange e = case e of
  Var var -> 1 + varIdx var
  Local local -> cacheFreeVarRange $ localCache local
  Constant _ -> 0
  Sort _ -> 0
  Lambda lam -> cacheFreeVarRange $ bindingCache lam
  Pi pi -> cacheFreeVarRange $ bindingCache pi
  App app -> cacheFreeVarRange $ appCache app
  Let lett -> cacheFreeVarRange $ letCache lett

hasFreeVars :: Expr -> Bool
hasFreeVars e = getFreeVarRange e > 0

closed :: Expr -> Bool
closed e = not $ hasFreeVars e

{- `has` functions -}

exprHasLocal :: Expr -> Bool
exprHasLocal e = case e of
  Var _ -> False
  Local _ -> True
  Sort _ -> False
  Constant _ -> False
  Lambda lam -> cacheHasLocal $ bindingCache lam
  Pi pi -> cacheHasLocal $ bindingCache pi
  App app -> cacheHasLocal $ appCache app
  Let lett -> cacheHasLocal $ letCache lett

exprHasLevelParam :: Expr -> Bool
exprHasLevelParam e = case e of
  Var var -> False
  Local local -> cacheHasLevelParam $ localCache local
  Constant const -> any (==True) (map levelHasParam (constLevels const))
  Sort sort -> levelHasParam (sortLevel sort)
  Lambda lam -> cacheHasLevelParam $ bindingCache lam
  Pi pi -> cacheHasLevelParam $ bindingCache pi
  App app -> cacheHasLevelParam $ appCache app
  Let lett -> cacheHasLevelParam $ letCache lett

{- N-ary applications -}

getOperator :: Expr -> Expr
getOperator e = case e of
  App app -> getOperator (appFn app)
  _ -> e

getAppArgs :: Expr -> [Expr]
getAppArgs e = reverse (getAppRevArgs e)

getAppOpArgs :: Expr -> (Expr, [Expr])
getAppOpArgs e = (getOperator e, getAppArgs e)

getAppRevArgs :: Expr -> [Expr]
getAppRevArgs (App app) = appArg app : getAppRevArgs (appFn app)
getAppRevArgs _ = []

getAppOpRevArgs :: Expr -> (Expr, [Expr])
getAppOpRevArgs e = (getOperator e, getAppRevArgs e)

{- Constructors -}

mkVar :: Int -> Expr
mkVar v_idx = Var (VarData v_idx)

mkLocal :: Name -> Name -> Expr -> BinderInfo -> Expr
mkLocal name pp_name ty binfo = Local $ mkLocalData name pp_name ty binfo

mkLocalDefault :: Name -> Expr -> Expr
mkLocalDefault name ty = Local $ mkLocalDataDefault name ty

mkLocalData :: Name -> Name -> Expr -> BinderInfo -> LocalData
mkLocalData name pp_name ty binfo = LocalData name pp_name ty binfo
                                      (ExprCache True (exprHasLevelParam ty) (getFreeVarRange ty))

mkLocalDataDefault :: Name -> Expr -> LocalData
mkLocalDataDefault name ty = LocalData name name ty BinderDefault
                                      (ExprCache True (exprHasLevelParam ty) (getFreeVarRange ty))

mkSort :: Level -> Expr
mkSort l = Sort (SortData l)

mkConstant :: Name -> [Level] -> Expr
mkConstant name levels = Constant (ConstantData name levels)

mkApp :: Expr -> Expr -> Expr
mkApp fn arg = App (AppData fn arg (ExprCache
                                     (exprHasLocal fn || exprHasLocal arg)
                                     (exprHasLevelParam fn || exprHasLevelParam arg)
                                     (max (getFreeVarRange fn) (getFreeVarRange arg))))

mkAppSeq :: Expr -> [Expr] -> Expr
mkAppSeq op [] = op
mkAppSeq op (arg:args) = mkAppSeq (mkApp op arg) args

mkRevAppSeq :: Expr -> [Expr] -> Expr
mkRevAppSeq op [] = op
mkRevAppSeq op (arg:args) = mkApp (mkRevAppSeq op args) arg

dec :: Int -> Int
dec x = if x <= 0 then x else x - 1

mkBinding :: Bool -> Name -> Expr -> Expr -> BinderInfo -> Expr
mkBinding isPi name domain body binfo =
  let ecache = ExprCache
                (exprHasLocal domain || exprHasLocal body)
                (exprHasLevelParam domain || exprHasLevelParam body)
                (max (getFreeVarRange domain) (dec $ getFreeVarRange body)) in
  case isPi of
    True -> Pi (BindingData name domain body binfo ecache)
    False -> Lambda (BindingData name domain body binfo ecache)

mkPi :: Name -> Expr -> Expr -> BinderInfo -> Expr
mkPi = mkBinding True

mkPiDefault :: Expr -> Expr -> Expr
mkPiDefault domain body = mkPi noName domain body BinderDefault

mkLambda :: Name -> Expr -> Expr -> BinderInfo -> Expr
mkLambda = mkBinding False

mkLambdaDefault :: Expr -> Expr -> Expr
mkLambdaDefault domain body = mkLambda noName domain body BinderDefault

mkLet :: Name -> Expr -> Expr -> Expr -> Expr
mkLet n ty val body =
  let ecache = ExprCache
                (exprHasLocal ty || exprHasLocal val || exprHasLocal body)
                (exprHasLevelParam ty || exprHasLevelParam val || exprHasLevelParam body)
                (max (getFreeVarRange ty) (max (getFreeVarRange val) (dec $ getFreeVarRange body))) in
  Let (LetData n ty val body ecache)

mkArrow :: Expr -> Expr -> Expr
mkArrow = mkPiDefault

{- Updaters -}

updateLocal :: LocalData -> Expr -> Expr
updateLocal local new_type = mkLocal (localName local) (localPPName local) new_type (localInfo local)

updateBinding :: Bool -> BindingData -> Expr -> Expr -> Expr
updateBinding isPi bind new_domain new_body =
  mkBinding isPi (bindingName bind) new_domain new_body (bindingInfo bind)

updatePi :: BindingData -> Expr -> Expr -> Expr
updatePi = updateBinding True

updateLambda :: BindingData -> Expr -> Expr -> Expr
updateLambda = updateBinding False

updateApp :: AppData -> Expr -> Expr -> Expr
updateApp app new_fn new_arg = mkApp new_fn new_arg

updateLet :: LetData -> Expr -> Expr -> Expr -> Expr
updateLet lett newTy newVal newBody = mkLet (letName lett) newTy newVal newBody

updateConstant const levels = mkConstant (constName const) levels
updateSort sort level = mkSort level


{- Traversals -}

-- Replace
type Offset = Int
type ReplaceFn = (Expr -> Offset -> Maybe Expr)

replaceInExpr :: ReplaceFn -> Expr -> Expr
replaceInExpr f t = replaceInExprCore f t 0
  where
    replaceInExprCore :: ReplaceFn -> Expr -> Offset -> Expr
    replaceInExprCore f t offset =
      case f t offset of
        Just t0 -> t0
        Nothing ->
          case t of
            Local local -> updateLocal local (replaceInExprCore f (localType local) offset)
            App app -> updateApp app (replaceInExprCore f (appFn app) offset)
                       (replaceInExprCore f (appArg app) offset)
            Lambda lam -> updateLambda lam (replaceInExprCore f (bindingDomain lam) offset)
                          (replaceInExprCore f (bindingBody lam) (1+offset))
            Pi pi -> updatePi pi (replaceInExprCore f (bindingDomain pi) offset)
                     (replaceInExprCore f (bindingBody pi) (1+offset))
            Let lett -> updateLet lett (replaceInExprCore f (letType lett) offset)
                        (replaceInExprCore f (letVal lett) (offset))
                        (replaceInExprCore f (letBody lett) (offset+1))
            _ -> t


-- Find
type FindFn = (Expr -> Offset -> Bool)
findInExpr :: FindFn -> Expr -> Maybe Expr
findInExpr f t = findInExprCore f t 0
  where
    findInExprCore :: FindFn -> Expr -> Offset -> Maybe Expr
    findInExprCore f t offset =
      if f t offset then Just t else
        case t of
          Local local -> findInExprCore f (localType local) offset
          App app -> findInExprCore f (appFn app) offset `mplus` findInExprCore f (appArg app) offset
          Lambda lam -> findInExprCore f (bindingDomain lam) offset `mplus` findInExprCore f (bindingBody lam) (offset+1)
          Pi pi -> findInExprCore f (bindingDomain pi) offset `mplus` findInExprCore f (bindingBody pi) (offset+1)
          Let lett -> findInExprCore f (letType lett) offset `mplus` findInExprCore f (letVal lett) (offset) `mplus` findInExprCore f (letBody lett) (offset+1)
          _ -> Nothing

-- Instantiate
instantiateSeq :: Expr -> [Expr] -> Expr
instantiateSeq e substs = replaceInExpr (instantiateSeqFn substs) e
  where
    instantiateSeqFn :: [Expr] -> ReplaceFn
    instantiateSeqFn substs e offset
      | offset >= getFreeVarRange e = Just e

    instantiateSeqFn substs (Var var) offset
      | varIdx var >= offset && varIdx var < offset + length substs =
          Just $ liftFreeVars (substs !! (varIdx var - offset)) offset
      | varIdx var > offset = Just $ mkVar (varIdx var - length substs)

    instantiateSeqFn _ _ _ = Nothing

instantiate :: Expr -> Expr -> Expr
instantiate e subst = instantiateSeq e [subst]

-- Lift free vars
liftFreeVars :: Expr -> Int -> Expr
liftFreeVars e shift = replaceInExpr (liftFreeVarsFn shift) e
  where
    liftFreeVarsFn :: Offset -> ReplaceFn
    liftFreeVarsFn shift e offset
      | offset >= getFreeVarRange e = Just e

    liftFreeVarsFn shift (Var var) offset
      | varIdx var >= offset = Just $ mkVar (varIdx var + shift)

    liftFreeVarsFn _ _ _ = Nothing


-- Instantiate universe params
instantiateLevelParams :: Expr -> [Name] -> [Level] -> Expr
instantiateLevelParams e levelParamNames levels =
  replaceInExpr (instantiateLevelParamsFn levelParamNames levels) e
  where
    instantiateLevelParamsFn :: [Name] -> [Level] -> ReplaceFn
    instantiateLevelParamsFn levelParamNames levels e _
      | not (exprHasLevelParam e) = Just e

    instantiateLevelParamsFn levelParamNames levels (Constant const) _ =
      Just $ updateConstant const (map (instantiateLevel levelParamNames levels) (constLevels const))

    instantiateLevelParamsFn levelParamNames levels (Sort sort) _ =
      Just $ updateSort sort (instantiateLevel levelParamNames levels (sortLevel sort))

    instantiateLevelParamsFn _ _ _ _ = Nothing

-- Abstract locals

abstractPi local body = abstractBindingSeq True [local] body
abstractLambda local body = abstractBindingSeq False [local] body

abstractPiSeq locals body = abstractBindingSeq True locals body
abstractLambdaSeq locals body = abstractBindingSeq False locals body

abstractBindingSeq isPi locals body =
  let abstractBody = abstractLocals locals body
      abstractTypes = map (\(local,i) -> abstractLocals (List.take i locals) (localType local)) (zip locals [0..])
  in
   foldr (\(abstractType,local) new_body -> mkBinding isPi (localName local) abstractType new_body (localInfo local))
   abstractBody (zip abstractTypes locals)

abstractLocals locals body = replaceInExpr (abstractLocalsFn locals) body
  where
    abstractLocalsFn :: [LocalData] -> ReplaceFn
    abstractLocalsFn locals e offset
      | not (exprHasLocal e) = Just e

    abstractLocalsFn locals e@(Local l) offset =
      case List.findIndex (\local -> localName local == localName l) locals of
        Nothing -> Just e
        Just idx -> Just (mkVar $ offset + (length locals - 1 - idx))

    abstractLocalsFn _ _  _ = Nothing

-- Misc

mkProp :: Expr
mkProp = mkSort mkZero

innerBodyOfLambda :: Expr -> Expr
innerBodyOfLambda e = case e of
    Lambda lam -> innerBodyOfLambda (bindingBody lam)
    _ -> e

isConstant :: Expr -> Bool
isConstant (Constant _) = True
isConstant _ = False

maybeConstant :: Expr -> Maybe ConstantData
maybeConstant (Constant c) = Just c
maybeConstant _ = Nothing
