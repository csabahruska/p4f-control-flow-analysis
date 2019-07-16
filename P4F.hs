{-# LANGUAGE LambdaCase, RecordWildCards #-}
module P4F where

{-
  interpreter for abstract semantics
-}

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

type Id = String

type AExp = Exp

{-
  INVARIANTS:
    - globally unique names
-}

data Exp
  = Let (Id, AExp, AExp) Exp
  -- AExp: atomic expression
  | Var Id
  | Lam Id Exp
  deriving (Show, Eq, Ord)

{-
  TODO:
    - abstract interpreter
  QUESTION:
    - could we map the embedded language to the host language stack instead of the explicit one?
-}
data Addr
  = AddrInt     Int
  | AddrId      String
  | AddrExp     Exp
  | AddrExpEnv  Exp Env
  | AddrHalt
  deriving (Show, Eq, Ord)


type Lam    = Exp -- Lam constructor only
type Clo    = (Lam, Env)
type Env    = Map Id Addr
type Store  = Map Addr (Set Clo)
type Stack  = Map Addr (Set (Frame, Addr)) -- NOTE: KStore in the article: Addr -> P(Kont)
type Frame  = (Id, Exp, Env)

type Alloc = State Int

allocInt :: Alloc Addr
allocInt = state $ \i -> (AddrInt i, succ i)

alloc0CFA :: Id -> Addr
alloc0CFA = AddrId

allocK0 :: Exp -> Addr
allocK0 = AddrExp

allocKP4F :: Exp -> Env -> Addr
allocKP4F = AddrExpEnv

alloc :: Id -> (Exp, P4FState) -> Addr
alloc n _ = alloc0CFA n

allocK :: (Exp, P4FState) -> Exp -> Env -> Store -> Addr
allocK _ exp env _ = allocKP4F exp env

data P4FState
  = P4FState
  { sEnv        :: Env
  , sStore      :: Store
  , sStack      :: Stack
  , sStackAddr  :: Addr
  }
  deriving (Show, Eq, Ord)

abstractAtomicEval :: AExp -> Env -> Store -> Set Clo
abstractAtomicEval exp env store = case exp of
  Var n -> store Map.! (env Map.! n)
  Lam{} -> Set.singleton (exp, env)
  _ -> error $ "unsupported atomic expression: " ++ show exp

abstractEval :: Exp -> P4FState -> [(Exp, P4FState)]
abstractEval exp p4fState@P4FState{..} = case exp of
  Let (y, f, ae) e -> do
    (Lam x e', lamEnv) <- Set.toList $ abstractAtomicEval f sEnv sStore
    let env   = Map.insert x addr lamEnv
        store = Map.insertWith Set.union addr (abstractAtomicEval ae sEnv sStore) sStore
        addr  = alloc x (exp, p4fState)

        stack = Map.insertWith Set.union addrK (Set.singleton $ ((y, e, sEnv), sStackAddr)) sStack
        addrK = allocK (exp, p4fState) e' env store
    pure (e', P4FState env store stack addrK)

  -- atomic expression
  ae -> do
    ((x, e, envK), addrK) <- Set.toList $ sStack Map.! sStackAddr
    let env   = Map.insert x addr envK
        store = Map.insertWith Set.union addr (abstractAtomicEval ae sEnv sStore) sStore
        addr  = alloc x (exp, p4fState)
    pure (e, P4FState env store sStack addrK)

-- NOTE: store and stack are included in the collected state, it causes exponential blowup
fixExp :: Exp -> Set (Exp, P4FState)
fixExp e0 = go (Set.singleton (e0, P4FState mempty mempty mempty AddrHalt)) where
  go :: Set (Exp, P4FState) -> Set (Exp, P4FState)
  go s
    | sNext <- Set.fromList . concatMap (uncurry abstractEval) . Set.toList $ s
    , s /= sNext
    = go sNext
    | otherwise
    = s

-- global store widening

type Config = (Exp, Env, Addr)

widenedFixExp :: Exp -> (Set Config, Store, Stack)
widenedFixExp e0 = go (mempty, mempty, mempty) where

  initial = (e0, P4FState mempty mempty mempty AddrHalt)

  go :: (Set Config, Store, Stack) -> (Set Config, Store, Stack)
  go (reachable, store, stack) = (reachableNext, storeNext, stackNext) where
    s             = concatMap (uncurry abstractEval) $ initial : [(e, P4FState env store stack addrK) | (e, env, addrK) <- Set.toList reachable]
    reachableNext = Set.fromList [(e, sEnv, sStackAddr) | (e, P4FState{..}) <- s]
    storeNext     = Map.unionsWith Set.union [sStore | (_, P4FState{..}) <- s]
    stackNext     = Map.unionsWith Set.union [sStack | (_, P4FState{..}) <- s]
