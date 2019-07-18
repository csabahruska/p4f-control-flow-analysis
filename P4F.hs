{-# LANGUAGE LambdaCase, RecordWildCards, TupleSections #-}
module AAM where

{-
  interpreter for abstract semantics
-}

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Text.Show.Pretty

type Id = String

type AExp = Exp

{-
  INVARIANTS:
    - globally unique names
-}

data Exp
  = LetApp (Id, AExp, AExp) Exp
  | Let (Id, AExp) Exp
  -- AExp: atomic expression
  | Var Id
  | Lam Id Exp
  | Lit String
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
  | AddrIdExp   {addrId :: String, addrExp :: Exp}
  | AddrExp     {addrExp :: Exp}
  | AddrExpEnv  {addrExp :: Exp, addrEnv :: Env}
  | AddrAAC     Exp Env Exp Env Store
  | AddrHalt
  deriving (Show, Eq, Ord)

newtype KAddr = KAddr Addr
  deriving (Show, Eq, Ord)


type Lam    = Exp -- Lam constructor only
type Clo    = (Lam, Env)
type Env    = Map Id Addr
type Store  = Map Addr (Set Clo)
type Stack  = Map KAddr (Set (Frame, KAddr)) -- NOTE: KStore in the article: Addr -> P(Kont)
type Frame  = (Id, Exp, Env)

data P4FState
  = P4FState
  { sEnv        :: Env
  , sStore      :: Store
  , sStack      :: Stack
  , sStackAddr  :: KAddr
  }
  deriving (Show, Eq, Ord)

data AAM
  = AAM
  { alloc   :: Id -> (Exp, P4FState) -> Addr
  , allocK  :: (Exp, P4FState) -> Exp -> Env -> Store -> KAddr
  }

abstractAtomicEval :: AExp -> Env -> Store -> Set Clo
abstractAtomicEval exp env store = case exp of
  Var n -> store Map.! (env Map.! n)
  Lam{} -> Set.singleton (exp, env)
  Lit{} -> Set.singleton (exp, mempty)
  _ -> error $ "unsupported atomic expression: " ++ show exp

abstractEval :: AAM -> Exp -> P4FState -> [(Exp, P4FState)]
abstractEval AAM{..} exp p4fState@P4FState{..} = case exp of
  LetApp (y, f, ae) e -> do
    (Lam x e', lamEnv) <- Set.toList $ abstractAtomicEval f sEnv sStore
    let env   = Map.insert x addr lamEnv
        store = Map.insertWith Set.union addr (abstractAtomicEval ae sEnv sStore) sStore
        addr  = alloc x (exp, p4fState)

        stack = Map.insertWith Set.union addrK (Set.singleton $ ((y, e, sEnv), sStackAddr)) sStack
        addrK = allocK (exp, p4fState) e' env store
    pure (e', P4FState env store stack addrK)

  Let (y, ae) e -> do
    let env   = Map.insert y addr sEnv
        store = Map.insertWith Set.union addr (abstractAtomicEval ae sEnv sStore) sStore
        addr  = alloc y (exp, p4fState)
    pure (e, P4FState env store sStack sStackAddr)

--  Lit{} -> [(exp, p4fState)]
  _ | sStackAddr == KAddr AddrHalt -> []--[(exp, p4fState)]
  -- atomic expression
  ae -> do
    ((x, e, envK), addrK) <- Set.toList $ Map.findWithDefault (error $ "ae not found " ++ show sStackAddr ++ " exp: " ++ show ae) sStackAddr sStack
    --((x, e, envK), addrK) <- Set.toList $ Map.findWithDefault (mempty) sStackAddr sStack
    let env   = Map.insert x addr envK
        store = Map.insertWith Set.union addr (abstractAtomicEval ae sEnv sStore) sStore
        addr  = alloc x (exp, p4fState)
    pure (e, P4FState env store sStack addrK)

-- global store widening

type Config = (Exp, Env, KAddr)

widenedFixExp :: AAM -> Exp -> (Set Config, Store, Stack)
widenedFixExp aam e0 = go (mempty, mempty, mempty) where

  initial = (e0, P4FState mempty mempty mempty $ KAddr AddrHalt)

  go :: (Set Config, Store, Stack) -> (Set Config, Store, Stack)
  go i@(reachable, store, stack) = if i == iNext then i else go iNext where
    s             = concatMap (uncurry (abstractEval aam)) $ initial : [(e, P4FState env store stack addrK) | (e, env, addrK) <- Set.toList reachable]
    reachableNext = Set.fromList [(e, sEnv, sStackAddr) | (e, P4FState{..}) <- s]
    storeNext     = Map.unionsWith Set.union [sStore | (_, P4FState{..}) <- s]
    stackNext     = Map.unionsWith Set.union [sStack | (_, P4FState{..}) <- s]
    iNext         = (reachableNext, storeNext, stackNext)

workListFixExp :: AAM -> Exp -> (Set Config, Store, Stack)
workListFixExp aam e0 = go mempty mempty [initState] mempty where

  initState = (e0, mempty, KAddr AddrHalt)

  go store stack [] seen = (seen, store, stack)
  go store stack ((exp, env, addrK):todo) seen = go storeNext stackNext todoNext seenNext where
    s             = abstractEval aam exp (P4FState env store stack addrK)
    storeNext     = Map.unionsWith Set.union $ store : [sStore | (_, P4FState{..}) <- s]
    stackNext     = Map.unionsWith Set.union $ stack : [sStack | (_, P4FState{..}) <- s]
    new           = [cfg | (e, P4FState{..}) <- s, let cfg = (e, sEnv, sStackAddr), Set.notMember cfg seen || storeNotIn sStore store || stackNotIn sStack stack]
    todoNext      = new ++ todo
    seenNext      = Set.union seen $ Set.fromList new

storeNotIn :: Store -> Store -> Bool
storeNotIn small big = not $ Map.isSubmapOfBy Set.isSubsetOf small big

stackNotIn :: Stack -> Stack -> Bool
stackNotIn small big = not $ Map.isSubmapOfBy Set.isSubsetOf small big

-- value allocators

alloc0 :: Id -> (Exp, P4FState) -> Addr
alloc0 n (e, P4FState{..}) = AddrId n

alloc1 :: Id -> (Exp, P4FState) -> Addr
alloc1 n (e, P4FState{..}) = AddrIdExp n e

-- kontinuation allocators

allocK0 :: (Exp, P4FState) -> Exp -> Env -> Store -> KAddr
allocK0 (e, P4FState{..}) e' env store = KAddr $ AddrExp e'

allocKP4F :: (Exp, P4FState) -> Exp -> Env -> Store -> KAddr
allocKP4F (e, P4FState{..}) e' env store = KAddr $ AddrExpEnv e' env

p4f = AAM alloc1 allocKP4F

-- example
expId1 :: Exp
expId1 =
  LetApp ("id", Lam "a" $ Var "a",  Lam "x" $ Var "x") $
  LetApp ("y", Var "id", Lit "#t") $
  LetApp ("z", Var "id", Lit "#f") $
  Lit "#done"

expId2 :: Exp
expId2 =
  Let ("id", Lam "x" $ Var "x") $
  LetApp ("y", Var "id", Lit "#t") $
  LetApp ("z", Var "id", Lit "#f") $
  Lit "#done"

expId3 :: Exp
expId3 =
  Let ("id", Lam "x" $ Var "x") $
  Let ("f", Lam "y" $ LetApp ("f_result", Var "id", Var "y") $ Var "f_result") $
  LetApp ("a", Var "f", Lit "1") $
  LetApp ("b", Var "f", Lit "#t") $
  Lit "#done"

test1 exp = let (c,s,k) = simplifyAddr $ widenedFixExp p4f exp in pPrint ("Config", c, "Store", s, "Stack", k)
test2 exp = let (c,s,k) = simplifyAddr $ workListFixExp p4f exp in pPrint ("Config", c, "Store", s, "Stack", k)

--
-- utility prettyfier
--

-- pretty address conversion

type Alloc = State (Map Addr Addr)

intAddrM :: Addr -> Alloc Addr
intAddrM AddrHalt = pure AddrHalt
intAddrM k = do
  m <- get
  case Map.lookup k m of
    Just v
      -> pure v
    Nothing
      | v <- AddrInt (Map.size m)
      -> put (Map.insert k v m) >> pure v

visitAddrK :: KAddr -> Alloc KAddr
visitAddrK (KAddr a) = KAddr <$> intAddrM a

simplifyAddr :: (Set Config, Store, Stack) -> (Set Config, Store, Stack)
simplifyAddr result = evalState (go result) mempty where
  go (c, s, k) = do
    c2 <- forM (Set.toList c) visitConfig
    s2 <- visitStore s
    k2 <- visitStack k
    pure (Set.fromList c2, s2, k2)

  visitEnv :: Env -> Alloc Env
  visitEnv = traverse intAddrM

  visitStore :: Store -> Alloc Store
  visitStore s = do
    l <- forM (Map.toList s) $ \(k,c) -> do
      k2 <- intAddrM k
      c2 <- forM (Set.toList c) $ \(exp, env) -> do
        env2 <- visitEnv env
        pure (exp, env2)
      pure (k2, Set.fromList c2)
    pure $ Map.fromList l

  visitConfig :: Config -> Alloc Config
  visitConfig (exp, env, addrK) = (exp,,) <$> visitEnv env <*> visitAddrK addrK

  visitStack :: Stack -> Alloc Stack
  visitStack s = do
    l <- forM (Map.toList s) $ \(k,f) -> do
      k2 <- visitAddrK k
      f2 <- forM (Set.toList f) $ \((n, exp, env), addrK) -> do
        env2 <- visitEnv env
        addrK2 <- visitAddrK addrK
        pure ((n, exp, env2), addrK2)
      pure (k2, Set.fromList f2)
    pure $ Map.fromList l
