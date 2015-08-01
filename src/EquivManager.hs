{-|
Module      : EquivManager
Description : Union-find for caching is_def_eq
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Union-find for caching is_def_eq
-}
module EquivManager (is_equiv,add_equiv,empty_equiv_manager,EquivManager) where

import qualified Data.IntDisjointSet as DS
import Control.Monad.State

import qualified Data.Map as Map
import Data.Map (Map)

import Name
import Level
import Expression

-- TODO implement a disjoint-set data structure with Integers instead of Ints
type NodeRef = Int

data EquivManager = EquivManager { em_disjoint_set :: DS.IntDisjointSet, em_map :: Map Expression NodeRef }

empty_equiv_manager = EquivManager DS.empty Map.empty
  
is_equiv :: Expression -> Expression -> EquivManager -> (Bool,EquivManager)
is_equiv e1 e2 eqv = flip runState eqv $ do
  n1 <- to_node e1
  n2 <- to_node e2
  dset <- gets em_disjoint_set
  let (is_equiv,new_dset) = DS.equivalent n1 n2 dset in do
    modify (\em -> em { em_disjoint_set = new_dset })
    return is_equiv

add_equiv :: Expression -> Expression -> EquivManager -> EquivManager
add_equiv e1 e2 eqv = flip execState eqv $ do
  n1 <- to_node e1
  n2 <- to_node e2
  dset <- gets em_disjoint_set  
  modify (\em -> em { em_disjoint_set = DS.union n1 n2 dset })

to_node :: Expression -> State EquivManager NodeRef
to_node e = do
  m <- gets em_map
  dset <- gets em_disjoint_set
  case Map.lookup e m of
    Just n -> return n
    Nothing -> let n = DS.size dset in do
      modify (\em -> EquivManager (DS.insert n dset) (Map.insert e n m))
      return n

