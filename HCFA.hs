{-# LANGUAGE LambdaCase, RecordWildCards, TupleSections #-}
module HCFA where

{-
  interpreter for abstract semantics

  H-CFA: a Simplified Approach for Pushdown Control Flow Analysis
  https://pdfs.semanticscholar.org/b0b2/e40ef798714a6cfb9ad32fc75783a198a142.pdf
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

data Addr
  = AddrInt     Int
  | AddrId      String
  | AddrIdExp   {addrId :: String, addrExp :: Exp}
  | AddrIdExpKAddr  {addrId :: String, addrExp :: Exp, addrReturn :: KAddr}
  | AddrIdKAddr {addrId :: String, addrReturn :: KAddr}
  | AddrExp     {addrExp :: Exp}
  | AddrExpEnv  {addrExp :: Exp, addrEnv :: Env}
  | AddrAAC     Exp Env Exp Env Store
  | AddrExpExpHistory {aExp1 :: Exp, aExp2 :: Exp, aHist :: History}
  | AddrHalt
  deriving (Show, Eq, Ord)

newtype KAddr = KAddr Addr
  deriving (Show, Eq, Ord)

-- Abstract Machine with the AAM approach (abstracting abstract machines)

type Lam      = Exp -- Lam constructor only
type Clo      = (Lam, Env)
type Env      = Map Id Addr
type Store    = Map Addr (Set Clo)
type Stack    = Map KAddr (Set (Frame, KAddr)) -- NOTE: KStore in the article: Addr -> P(Kont)
type Frame    = (Id, Exp, Env, History)
type History  = Map Id Addr

data AAMState
  = AAMState
  { sEnv        :: Env
  , sStore      :: Store
  , sStack      :: Stack
  , sStackAddr  :: KAddr
  , sHistory    :: History
  }
  deriving (Show, Eq, Ord)

data AAM
  = AAM
  { alloc   :: Id -> (Exp, AAMState) -> Addr
  , allocK  :: (Exp, AAMState) -> Exp -> Env -> Store -> KAddr
  }

abstractAtomicEval :: AExp -> Env -> Store -> Set Clo
abstractAtomicEval exp env store = case exp of
  Var n -> store Map.! (env Map.! n)
  Lam{} -> Set.singleton (exp, env)
  Lit{} -> Set.singleton (exp, mempty)
  _ -> error $ "unsupported atomic expression: " ++ show exp

abstractEval :: AAM -> Exp -> AAMState -> [(Exp, AAMState)]
abstractEval AAM{..} exp aamState@AAMState{..} = case exp of
  LetApp (y, f, ae) e -> do
    (Lam x e', lamEnv) <- Set.toList $ abstractAtomicEval f sEnv sStore
    let env   = Map.insert x addr lamEnv
        store = Map.insertWith Set.union addr (abstractAtomicEval ae sEnv sStore) sStore
        addr  = alloc x (exp, aamState)
        hist  = Map.insert x addr sHistory

        stack = Map.insertWith Set.union addrK (Set.singleton $ ((y, e, sEnv, sHistory), sStackAddr)) sStack
        addrK = allocK (exp, aamState) e' env store
    pure (e', AAMState env store stack addrK hist)

  Let (y, ae) e -> do
    let env   = Map.insert y addr sEnv
        store = Map.insertWith Set.union addr (abstractAtomicEval ae sEnv sStore) sStore
        addr  = alloc y (exp, aamState)
        hist  = Map.insert y addr sHistory
    pure (e, AAMState env store sStack sStackAddr hist)

--  Lit{} -> [(exp, aamState)]
  _ | sStackAddr == KAddr AddrHalt -> []--[(exp, aamState)]
  -- atomic expression
  ae -> do
    ((x, e, envK, histK), addrK) <- Set.toList $ Map.findWithDefault (error $ "ae not found " ++ show sStackAddr ++ " exp: " ++ show ae) sStackAddr sStack
    --((x, e, envK), addrK) <- Set.toList $ Map.findWithDefault (mempty) sStackAddr sStack
    let env   = Map.insert x addr envK
        store = Map.insertWith Set.union addr (abstractAtomicEval ae sEnv sStore) sStore
        addr  = alloc x (exp, aamState)
        hist  = Map.insert x addr histK
    pure (e, AAMState env store sStack addrK hist)

-- global store widening

type Config = (Exp, Env, KAddr, History)

widenedFixExp :: AAM -> Exp -> (Set Config, Store, Stack)
widenedFixExp aam e0 = go (mempty, mempty, mempty) where

  initState :: (Exp, AAMState)
  initState = (e0, AAMState mempty mempty mempty (KAddr AddrHalt) mempty)

  go :: (Set Config, Store, Stack) -> (Set Config, Store, Stack)
  go i@(reachable, store, stack) = if i == iNext then i else go iNext where
    s             = concatMap (uncurry (abstractEval aam)) $ initState : [(e, AAMState env store stack addrK hist) | (e, env, addrK, hist) <- Set.toList reachable]
    reachableNext = Set.fromList [(e, sEnv, sStackAddr, sHistory) | (e, AAMState{..}) <- s]
    storeNext     = Map.unionsWith Set.union [sStore | (_, AAMState{..}) <- s]
    stackNext     = Map.unionsWith Set.union [sStack | (_, AAMState{..}) <- s]
    iNext         = (reachableNext, storeNext, stackNext)

workListFixExp :: AAM -> Exp -> (Set Config, Store, Stack)
workListFixExp aam e0 = go mempty mempty [initState] mempty where

  initState :: Config
  initState = (e0, mempty, KAddr AddrHalt, mempty)

  go :: Store -> Stack -> [Config] -> Set Config -> (Set Config, Store, Stack)
  go store stack [] seen = (seen, store, stack)
  go store stack ((exp, env, addrK, hist):todo) seen = go storeNext stackNext todoNext seenNext where
    s             = abstractEval aam exp (AAMState env store stack addrK hist)
    storeNext     = Map.unionsWith Set.union $ store : [sStore | (_, AAMState{..}) <- s]
    stackNext     = Map.unionsWith Set.union $ stack : [sStack | (_, AAMState{..}) <- s]
    new           = [cfg | (e, AAMState{..}) <- s, let cfg = (e, sEnv, sStackAddr, sHistory), Set.notMember cfg seen || storeNotIn sStore store || stackNotIn sStack stack]
    todoNext      = new ++ todo
    seenNext      = Set.union seen $ Set.fromList new

  storeNotIn :: Store -> Store -> Bool
  storeNotIn small big = not $ Map.isSubmapOfBy Set.isSubsetOf small big

  stackNotIn :: Stack -> Stack -> Bool
  stackNotIn small big = not $ Map.isSubmapOfBy Set.isSubsetOf small big

-- value allocators

alloc0 :: Id -> (Exp, AAMState) -> Addr
alloc0 n (e, AAMState{..}) = AddrId n

alloc1 :: Id -> (Exp, AAMState) -> Addr
alloc1 n (e, AAMState{..}) = AddrIdExp n e

alloc0H :: Id -> (Exp, AAMState) -> Addr
alloc0H n (e, AAMState{..}) = AddrIdKAddr n sStackAddr

alloc1H :: Id -> (Exp, AAMState) -> Addr
alloc1H n (e, AAMState{..}) = AddrIdExpKAddr n e sStackAddr

-- kontinuation allocators

allocK0 :: (Exp, AAMState) -> Exp -> Env -> Store -> KAddr
allocK0 (e, AAMState{..}) e' env store = KAddr $ AddrExp e'

allocKP4F :: (Exp, AAMState) -> Exp -> Env -> Store -> KAddr
allocKP4F (e, AAMState{..}) e' env store = KAddr $ AddrExpEnv e' env

allocKH :: (Exp, AAMState) -> Exp -> Env -> Store -> KAddr
allocKH (e, AAMState{..}) e' env store = KAddr $ AddrExpExpHistory e e' sHistory

-- CFA alorithm configuration

p4f = AAM alloc1 allocKP4F
p4fH0 = AAM alloc0H allocKP4F
p4fH1 = AAM alloc1H allocKP4F
hCFA = AAM alloc0 allocKH

-- examples

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

expId4 :: Exp
expId4 =
  Let ("id", Lam "x" $ Var "x") $
  LetApp ("y", Var "id", Var "id") $
  LetApp ("z", Var "y", Lit "#f") $
  LetApp ("q", Var "y", Lit "1") $
  Lit "#done"

test1 exp = let (c,s,k) = simplifyAddr $ widenedFixExp p4fH1 exp  in pPrint ("Config", c, "Store", s, "Stack", k)
test2 exp = let (c,s,k) = simplifyAddr $ workListFixExp hCFA exp in pPrint ("Config", c, "Store", s, "Stack", k)

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
  visitConfig (exp, env, addrK, hist) = (exp,,,) <$> visitEnv env <*> visitAddrK addrK <*> visitEnv hist

  visitStack :: Stack -> Alloc Stack
  visitStack s = do
    l <- forM (Map.toList s) $ \(k,f) -> do
      k2 <- visitAddrK k
      f2 <- forM (Set.toList f) $ \((n, exp, env, hist), addrK) -> do
        env2 <- visitEnv env
        hist2 <- visitEnv hist
        addrK2 <- visitAddrK addrK
        pure ((n, exp, env2, hist2), addrK2)
      pure (k2, Set.fromList f2)
    pure $ Map.fromList l
