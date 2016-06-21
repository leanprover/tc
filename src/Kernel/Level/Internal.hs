{-|
Module      : Kernel.Level.Internal
Description : Universe levels
Copyright   : (c) Daniel Selsam, 2016
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Implementation of universe levels
-}
module Kernel.Level.Internal where

import Kernel.Name
import Lens.Simple
import Data.List as List
import Control.Monad

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import Data.List (elemIndex, sortBy, genericLength)

newtype SuccData = SuccData { succOf :: Level } deriving (Eq,Show,Ord)
data MaxCoreData = MaxCoreData { isImax :: Bool, maxLHS :: Level, maxRHS :: Level } deriving (Eq,Show,Ord)

data Level = Zero
           | Succ SuccData
           | Max MaxCoreData
           | IMax MaxCoreData
           | LevelParam Name
           | GlobalLevel Name
           deriving (Eq, Ord)

showLevel :: Level -> String
showLevel l = case toLevelOffset l of
  (l,0) -> "{ " ++ showLevelCore l ++ " }"
  (l,k) -> "{ <" ++ show k ++ "> " ++ showLevelCore l ++ " }"
  where
    showLevelCore :: Level -> String
    showLevelCore l = case l of
      Zero -> "0"
      Max max -> "(max " ++ showLevel (maxLHS max) ++ " " ++ showLevel (maxRHS max) ++ ")"
      IMax imax -> "(max " ++ showLevel (maxLHS imax) ++ " " ++ showLevel (maxRHS imax) ++ ")"
      LevelParam lp -> show lp
      GlobalLevel gl -> "!" ++ show gl

instance Show Level where show e = showLevel e


getUndefParam :: Level -> [Name] -> Maybe Name
getUndefParam l ns = case l of
  Zero -> Nothing
  Succ succ -> getUndefParam (succOf succ) ns
  Max max -> getUndefParam (maxLHS max) ns `mplus` getUndefParam (maxRHS max) ns
  IMax imax -> getUndefParam (maxLHS imax) ns `mplus` getUndefParam (maxRHS imax) ns
  LevelParam n -> if elem n ns then Nothing else Just n
  GlobalLevel n -> Nothing

getUndefGlobal :: Level -> Set Name -> Maybe Name
getUndefGlobal l ns = case l of
  Zero -> Nothing
  Succ succ -> getUndefGlobal (succOf succ) ns
  Max max -> getUndefGlobal (maxLHS max) ns `mplus` getUndefGlobal (maxRHS max) ns
  IMax imax -> getUndefGlobal (maxLHS imax) ns `mplus` getUndefGlobal (maxRHS imax) ns
  LevelParam n -> Nothing
  GlobalLevel n -> if Set.member n ns then Nothing else Just n

-- A level is explicit if it is of the form 'Succ^k Zero' for some 'k'.
isExplicit l = case l of
  Zero -> True
  Succ succ -> isExplicit (succOf succ)
  Max max -> False
  IMax imax -> False
  LevelParam n -> False
  GlobalLevel n -> False

getDepth l = case l of
  Zero -> 0
  Succ succ -> 1 + getDepth (succOf succ)
  Max max -> 0
  IMax imax -> 0
  LevelParam n -> 0
  GlobalLevel n -> 0

-- Factors out outermost sequence of 'mkSucc' applications.
toLevelOffset l = case l of
  Succ succ -> over _2 (+1) $ toLevelOffset (succOf succ)
  otherwise -> (l,0)

isZero l = case l of
  Zero -> True
  _ -> False

mkZero = Zero
mkSucc l = Succ (SuccData l)

mkLevelOne = mkSucc mkZero
mkLevelTwo = mkSucc $ mkSucc mkZero

mkIteratedSucc l k
  | k == 0 = l
  | k > 0 = Succ (SuccData (mkIteratedSucc l (k-1)))

mkMax l1 l2
  | isExplicit l1 && isExplicit l2 = if getDepth l1 >= getDepth l2 then l1 else l2
  | l1 == l2 = l1
  | isZero l1 = l2
  | isZero l2 = l1
  | otherwise =
    case l1 of
      Max max | maxLHS max == l2 || maxRHS max == l2 -> l1
      otherwise ->
        case l2 of
          Max max | maxLHS max == l1 || maxRHS max == l1 -> l2
          otherwise ->
            let (l1',k1) = toLevelOffset l1
                (l2',k2) = toLevelOffset l2
            in
             if l1' == l2' then (if k1 >= k2 then l1 else l2) else Max (MaxCoreData False l1 l2)

mkIMax l1 l2
  | isDefinitelyNotZero l2 = mkMax l1 l2
  | isZero l2 = l2
  | isZero l1 = l2
  | l1 == l2 = l1
  | otherwise = IMax (MaxCoreData True l1 l2)

mkLevelParam = LevelParam
mkGlobalLevel = GlobalLevel

isDefinitelyNotZero l = case l of
  Zero -> False
  LevelParam _ -> False
  GlobalLevel _ -> False
  Succ _ -> True
  Max max -> isDefinitelyNotZero (maxLHS max) || isDefinitelyNotZero (maxRHS max)
  IMax imax -> isDefinitelyNotZero (maxRHS imax)

levelHasParam l = case l of
  LevelParam _ -> True
  Succ succ -> levelHasParam (succOf succ)
  Max max -> levelHasParam (maxLHS max) || levelHasParam (maxRHS max)
  IMax imax -> levelHasParam (maxLHS imax) || levelHasParam (maxRHS imax)
  _ -> False


levelKindRank l = case l of
  Zero -> 0
  Succ _ -> 1
  Max _ -> 2
  IMax _ -> 3
  LevelParam _ -> 4
  GlobalLevel _ -> 5

levelNormCmp l1 l2 = if l1 == l2 then EQ else levelNormCmpCore (toLevelOffset l1) (toLevelOffset l2)

levelNormCmpCore (l1,k1) (l2,k2)
  | l1 == l2 = compare k1 k2
  | levelKindRank l1 /= levelKindRank l2 = compare (levelKindRank l1) (levelKindRank l2)
  | otherwise =
    case (l1,l2) of
      (LevelParam n1,LevelParam n2) -> compare n1 n2
      (GlobalLevel n1,GlobalLevel n2) -> compare n1 n2
      (Max max1,Max max2) -> levelNormCmpMaxCore max1 max2
      (IMax max1,IMax max2) -> levelNormCmpMaxCore max1 max2

levelNormCmpMaxCore (MaxCoreData _ l1a l2a) (MaxCoreData _ l1b l2b)
  | l1a /= l1b = levelNormCmp l1a l1b
  | otherwise = levelNormCmp l2a l2b

collectMaxArgs (Max (MaxCoreData False l1 l2)) = collectMaxArgs l1 ++ collectMaxArgs l2
collectMaxArgs l = [l]

-- called on sorted explicits
removeSmallExplicits [] = Nothing
removeSmallExplicits [l] = Just l
removeSmallExplicits (l:ls) = removeSmallExplicits ls

normalizeLevel l = let p = toLevelOffset l in case fst p of
  Zero -> l
  LevelParam _ -> l
  GlobalLevel _ -> l
  IMax (MaxCoreData True l1 l2) ->
    let l1_n = normalizeLevel l1
        l2_n = normalizeLevel l2
    in
     if l1 /= l1_n || l2 /= l2_n then mkIteratedSucc (mkIMax l1_n l2_n) (snd p) else l
  Max max ->
    let maxArgs = (sortBy levelNormCmp) . concat . (map (collectMaxArgs . normalizeLevel)) $ collectMaxArgs (Max max)
        explicit = removeSmallExplicits $ filter isExplicit maxArgs
        nonExplicits = let rest = filter (not . isExplicit) maxArgs
                           (butLast,last) = foldl (\ (keep,prev) curr ->
                                                      if fst (toLevelOffset prev) == fst (toLevelOffset curr)
                                                      then (keep,curr)
                                                      else (keep ++ [prev],curr))
                                              ([],head rest)
                                              (tail rest)
                        in butLast ++ [last]
        explicits = case explicit of
          Nothing -> []
          Just x -> if snd (toLevelOffset x) <= maximum (map (snd . toLevelOffset) nonExplicits) then [] else [x]
        allArgs = explicits ++ nonExplicits
        liftedArgs = map (flip mkIteratedSucc (snd p)) allArgs
    in
     mkBigMax liftedArgs

mkBigMax [] = mkZero
mkBigMax [l] = l
mkBigMax (x:xs) = mkMax x (mkBigMax xs)

-- Check whether two levels are equivalent (modulo normalizing 'max')
levelEquiv l1 l2 = l1 == l2 || normalizeLevel l1 == normalizeLevel l2

-- Replace

type LevelReplaceFn = (Level -> Maybe Level)

replaceInLevel :: LevelReplaceFn -> Level -> Level
replaceInLevel f l =
  case f l of
    Just l0 -> l0
    Nothing ->
      case l of
        Zero -> l
        Succ succ -> mkSucc (replaceInLevel f $ succOf succ)
        Max max -> mkMax (replaceInLevel f $ maxLHS max) (replaceInLevel f $ maxRHS max)
        IMax imax -> mkIMax (replaceInLevel f $ maxLHS imax) (replaceInLevel f $ maxRHS imax)
        LevelParam _ -> l
        GlobalLevel _ -> l


instantiateLevel :: [Name] -> [Level] -> Level -> Level
instantiateLevel lpNames levels level =
  replaceInLevel (instantiateLevelFn lpNames levels) level
  where
    instantiateLevelFn :: [Name] -> [Level] -> LevelReplaceFn
    instantiateLevelFn lpNames levels level
      | not (genericLength lpNames == genericLength levels) = error "Wrong number of level params"
      | not (levelHasParam level) = Just level

    instantiateLevelFn lpNames levels (LevelParam name) =
      case elemIndex name lpNames of
        Nothing -> Nothing
        Just idx -> Just (levels!!idx)

    instantiateLevelFn _ _ _ = Nothing

-- Order
levelNotBiggerThan l1 l2 = levelNotBiggerThanCore (normalizeLevel l1) (normalizeLevel l2) where
  levelNotBiggerThanCore l1 l2
    | l1 == l2 || isZero l1 = True

  levelNotBiggerThanCore (Max max) l2 = levelNotBiggerThan (maxLHS max) l2 && levelNotBiggerThan (maxRHS max) l2
  levelNotBiggerThanCore l1 (Max max)
    | levelNotBiggerThan l1 (maxLHS max) || levelNotBiggerThan l1 (maxRHS max) = True

  levelNotBiggerThanCore (IMax imax) l2 = levelNotBiggerThan (maxLHS imax) l2 && levelNotBiggerThan (maxRHS imax) l2
  levelNotBiggerThanCore l1 (IMax imax) = levelNotBiggerThan l1 (maxRHS imax)

  levelNotBiggerThanCore l1 l2 =
    let (l1',k1) = toLevelOffset l1
        (l2',k2) = toLevelOffset l2
    in
     if l1' == l2' || isZero l1' then k1 <= k2 else
       if k1 == k2 && k1 > 0 then levelNotBiggerThan l1' l2' else
         False

maybeParamName :: Level -> Maybe Name
maybeParamName l = case l of
                    LevelParam n -> Just n
                    _ -> Nothing
