{-
Copyright (c) 2015 Daniel Selsam.

This file is part of the Lean reference type checker.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
-}

module Level where
import Control.Monad
import Name

import Data.List (elemIndex,sortBy,genericLength)

import qualified Data.Set as Set
import Data.Set (Set)

newtype SuccData = SuccData { succ_of :: Level } deriving (Eq,Show)
data MaxCoreData = MaxCoreData { is_imax :: Bool, max_lhs :: Level, max_rhs :: Level } deriving (Eq,Show)
newtype LevelParamData = LevelParamData { param_name :: Name } deriving (Eq,Show)
newtype GlobalLevelData = GlobalLevelData { global_name :: Name } deriving (Eq,Show)

-- TODO inefficient
data Level = Zero
           | Succ SuccData
           | Max MaxCoreData
           | IMax MaxCoreData
           | LevelParam Name
           | GlobalLevel Name
           deriving (Eq,Show)


  

get_undef_param :: Level -> [Name] -> Maybe Name
get_undef_param l ns = case l of
  Zero -> Nothing
  Succ succ -> get_undef_param (succ_of succ) ns
  Max max -> get_undef_param (max_lhs max) ns `mplus` get_undef_param (max_rhs max) ns
  IMax imax -> get_undef_param (max_lhs imax) ns `mplus` get_undef_param (max_rhs imax) ns
  LevelParam n -> if elem n ns then Nothing else Just n
  GlobalLevel n -> Nothing

get_undef_global :: Level -> Set Name -> Maybe Name
get_undef_global l ns = case l of
  Zero -> Nothing
  Succ succ -> get_undef_global (succ_of succ) ns
  Max max -> get_undef_global (max_lhs max) ns `mplus` get_undef_global (max_rhs max) ns
  IMax imax -> get_undef_global (max_lhs imax) ns `mplus` get_undef_global (max_rhs imax) ns
  LevelParam n -> Nothing
  GlobalLevel n -> if Set.member n ns then Nothing else Just n

{- |
A level is explicit if it is of the form 'Succ^k Zero' for some 'k'.

>>> is_explicit mk_level_zero
True  

>>> is_explicit (mk_succ (mk_succ mk_level_zero))
True

>>> is_explicit (mk_max (mk_level_param (mk_name ["l"])) mk_level_zero)
False
-}
is_explicit l = case l of
  Zero -> True
  Succ succ -> is_explicit (succ_of succ)
  Max max -> False
  IMax imax -> False
  LevelParam n -> False
  GlobalLevel n -> False

get_depth l = case l of
  Zero -> 0
  Succ succ -> 1 + get_depth (succ_of succ)
  Max max -> 0
  IMax imax -> 0
  LevelParam n -> 0
  GlobalLevel n -> 0

{- |
Factors out outermost sequence of 'mk_succ' applications.

>>> to_offset mk_level_zero
(Zero,0)

>>> to_offset (mk_succ mk_level_zero)
(Zero,1)

>>> to_offset (mk_succ (mk_level_param (mk_name ["l"])))
(LevelParam .l,1)
-}
to_offset l = case l of
  Succ succ -> (\(p,q) -> (p,q+1)) $ to_offset (succ_of succ)
  otherwise -> (l,0)
  
is_zero l = case l of
  Zero -> True
  _ -> False

mk_level_zero = Zero
mk_succ l = Succ (SuccData l)

mk_level_one = mk_succ mk_level_zero
mk_level_two = mk_succ $ mk_succ mk_level_zero

mk_iterated_succ l k
  | k == 0 = l
  | k > 0 = Succ (SuccData (mk_iterated_succ l (k-1)))

mk_max l1 l2
  | is_explicit l1 && is_explicit l2 = if get_depth l1 >= get_depth l2 then l1 else l2
  | l1 == l2 = l1
  | is_zero l1 = l2
  | is_zero l2 = l1
  | otherwise =
    case l1 of
      Max max | max_lhs max == l2 || max_rhs max == l2 -> l1
      otherwise ->
        case l2 of
          Max max | max_lhs max == l1 || max_rhs max == l1 -> l2
          otherwise -> 
            let (l1',k1) = to_offset l1
                (l2',k2) = to_offset l2
            in
             if l1' == l2' then (if k1 >= k2 then l1 else l2) else Max (MaxCoreData False l1 l2)

mk_imax l1 l2
  | is_definitely_not_zero l2 = mk_max l1 l2
  | is_zero l2 = l2
  | is_zero l1 = l2
  | l1 == l2 = l1
  | otherwise = IMax (MaxCoreData True l1 l2)

mk_level_param = LevelParam
mk_global_univ = GlobalLevel

is_definitely_not_zero l = case l of
  Zero -> False
  LevelParam _ -> False
  GlobalLevel _ -> False
  Succ _ -> True
  Max max -> is_definitely_not_zero (max_lhs max) || is_definitely_not_zero (max_rhs max)
  IMax imax -> is_definitely_not_zero (max_rhs imax)  

has_param l = case l of
  LevelParam _ -> True
  Succ succ -> has_param (succ_of succ)
  Max max -> has_param (max_lhs max) || has_param (max_rhs max)
  IMax imax -> has_param (max_lhs imax) || has_param (max_rhs imax)
  _ -> False


-- TODO put LevelKind in another name space and import qualified?
level_kind_rank l = case l of
  Zero -> 0
  Succ _ -> 1
  Max _ -> 2
  IMax _ -> 3
  LevelParam _ -> 4
  GlobalLevel _ -> 5

level_norm_cmp l1 l2 = if l1 == l2 then EQ else level_norm_cmp_core (to_offset l1) (to_offset l2)
                
level_norm_cmp_core (l1,k1) (l2,k2)
  | l1 == l2 = compare k1 k2
  | level_kind_rank l1 /= level_kind_rank l2 = compare (level_kind_rank l1) (level_kind_rank l2)
  | otherwise =
    case (l1,l2) of
      (LevelParam n1,LevelParam n2) -> compare n1 n2
      (GlobalLevel n1,GlobalLevel n2) -> compare n1 n2
      (Max max1,Max max2) -> level_norm_cmp_max_core max1 max2
      (IMax max1,IMax max2) -> level_norm_cmp_max_core max1 max2      

level_norm_cmp_max_core (MaxCoreData _ l1a l2a) (MaxCoreData _ l1b l2b)
  | l1a /= l1b = level_norm_cmp l1a l1b
  | otherwise = level_norm_cmp l2a l2b

collect_max_args (Max (MaxCoreData False l1 l2)) = collect_max_args l1 ++ collect_max_args l2
collect_max_args l = [l]

-- called on sorted explicits
remove_small_explicits [] = Nothing
remove_small_explicits [l] = Just l
remove_small_explicits (l:ls) = remove_small_explicits ls

-- TODO we need to sort and simplify MAX
-- Right now we will fail when two identical universes are syntatically different
normalize_level l = let p = to_offset l in case fst p of
  Zero -> l
  LevelParam _ -> l
  GlobalLevel _ -> l
  IMax (MaxCoreData True l1 l2) ->
    let l1_n = normalize_level l1
        l2_n = normalize_level l2
    in
     if l1 /= l1_n || l2 /= l2_n then mk_iterated_succ (mk_imax l1_n l2_n) (snd p) else l
  Max max ->
    let max_args = (sortBy level_norm_cmp) . (map normalize_level) $ collect_max_args (Max max)
        explicit = remove_small_explicits $ filter is_explicit max_args
        -- TODO confirm that I don't need to check that the offsets are ordered here (Leo does for some reason)        
        non_explicits = let rest = filter (not . is_explicit) max_args
                            (but_last,last) = foldl (\ (keep,prev) curr ->
                                                      if fst (to_offset prev) == fst (to_offset curr)
                                                      then (keep,curr)
                                                      else (keep ++ [prev],curr))
                                              ([],head rest)
                                              (tail rest)
                        in but_last ++ [last]
        explicits = case explicit of
          Nothing -> []
          Just x -> if snd (to_offset x) < maximum (map (snd . to_offset) non_explicits) then [] else [x]
        all_args = explicits ++ non_explicits
        lifted_args = map (flip mk_iterated_succ (snd p)) all_args
    in
     mk_big_max lifted_args

mk_big_max [] = mk_level_zero
mk_big_max [l] = l
mk_big_max (x:xs) = mk_max x (mk_big_max xs)

    
level_equiv l1 l2 = l1 == l2 || normalize_level l1 == normalize_level l2


-- Replace

type LevelReplaceFn = (Level -> Maybe Level)

replace_in_level :: LevelReplaceFn -> Level -> Level
replace_in_level f l =
  case f l of
    Just l0 -> l0
    Nothing ->
      case l of
        Zero -> l
        Succ succ -> mk_succ (replace_in_level f $ succ_of succ)
        Max max -> mk_max (replace_in_level f $ max_lhs max) (replace_in_level f $ max_rhs max)
        IMax imax -> mk_imax (replace_in_level f $ max_lhs imax) (replace_in_level f $ max_rhs imax)
        LevelParam param -> l
        GlobalLevel global -> l

instantiate_level_fn :: [Name] -> [Level] -> LevelReplaceFn
instantiate_level_fn level_param_names levels level
  | not (genericLength level_param_names == genericLength levels) = error "Wrong number of level params"
  | not (has_param level) = Just level

instantiate_level_fn level_param_names levels (LevelParam name) =
  case elemIndex name level_param_names of
    Nothing -> Nothing
    Just idx -> Just (levels!!idx)

instantiate_level_fn _ _ _ = Nothing

instantiate_level :: [Name] -> [Level] -> Level -> Level
instantiate_level level_param_names levels level =
  replace_in_level (instantiate_level_fn level_param_names levels) level

-- Order

-- TODO [level_leq_core] was rushed, need to test carefully
level_leq l1 l2 = level_leq_core (normalize_level l1) (normalize_level l2)
level_leq_core l1 l2
  | l1 == l2 || is_zero l1 = True

level_leq_core (Max max) l2 = level_leq (max_lhs max) l2 && level_leq (max_rhs max) l2
level_leq_core l1 (Max max) = level_leq l1 (max_lhs max) || level_leq l1 (max_rhs max)
level_leq_core (IMax imax) l2 = level_leq (max_lhs imax) l2 && level_leq (max_rhs imax) l2
level_leq_core l1 (IMax imax) = level_leq l1 (max_rhs imax)

level_leq_core l1 l2 =
  let (l1',k1) = to_offset l1
      (l2',k2) = to_offset l2
  in
   if l1' == l2' || is_zero l1' then k1 <= k2 else
     if k1 == k2 && k1 > 0 then level_leq l1' l2' else
       False


instance Ord Level where
  (<=) = level_leq
