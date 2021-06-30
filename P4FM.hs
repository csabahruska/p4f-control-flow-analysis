{-# LANGUAGE RecordWildCards, LambdaCase #-}
module P4FM where

import Control.Monad.List
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
  = LetApp (Id, AExp, AExp) Exp
  | Let (Id, AExp) Exp
  -- AExp: atomic expression
  | Var Id
  | Lam Id Exp
  | Lit String
  deriving (Show, Eq, Ord)

data Addr
  = AddrInt         Int -- NOTE: only for the pretty printer
  | AddrId          String
  | AddrIdExp       {addrId :: String, addrExp :: Exp}
  | AddrIdExpKAddr  {addrId :: String, addrExp :: Exp, addrReturn :: KAddr}
  | AddrIdKAddr     {addrId :: String, addrReturn :: KAddr}
  | AddrExp         {addrExp :: Exp}
  | AddrExpEnv      {addrExp :: Exp, addrEnv :: Env}
  | AddrAAC         Exp Env Exp Env Store
  | AddrHalt
  deriving (Show, Eq, Ord)

newtype KAddr = KAddr Addr
  deriving (Show, Eq, Ord)

-- Abstract Machine with the AAM approach (abstracting abstract machines)

type Lam    = Exp -- Lam constructor only
type Clo    = (Lam, Env)
type Env    = Map Id Addr
type Store  = Map Addr (Set Clo)
type Stack  = Map KAddr (Set (Frame, KAddr)) -- NOTE: KStore in the article: Addr -> P(Kont)
type Frame  = (Id, Exp, Env)

data AAMState
  = AAMState
  { sStore      :: Store
  , sStack      :: Stack
  , sStackTop   :: KAddr
  }
  deriving (Show, Eq, Ord)

type M = StateT AAMState (ListT D)
type D = StateT Int IO

{-
  Env and Store
-}
extendEnv :: Id -> Addr -> Env -> Env
extendEnv var addr env = Map.insert var addr env

extendStore :: Set Clo -> Addr -> M ()
extendStore val addr = do
  modify' $ \s@AAMState{..} -> s {sStore = Map.insertWith Set.union addr val sStore}

{-
  Allocator
-}
alloc :: Id -> Exp -> M Addr
alloc var exp = do
  -- TODO: use the right abstract allocator
  lift . lift . state $ \i -> (AddrInt i, succ i)

allocK :: M KAddr
allocK = do
  -- TODO: use the right abstract allocator
  lift . lift . state $ \i -> (KAddr $ AddrInt i, succ i)

{-
  Stack
-}
stackPush :: Frame -> M ()
stackPush frame = do
  newStackTop <- allocK -- TODO: add access to the necessary information
  oldStackTop <- gets sStackTop
  let frameContinuation = Set.singleton (frame, oldStackTop)
  modify' $ \s@AAMState{..} -> s
    { sStack    = Map.insertWith Set.union newStackTop frameContinuation sStack
    , sStackTop = newStackTop
    }

stackPop :: M Frame
stackPop = do
  oldStackTop <- gets sStackTop
  when (oldStackTop == KAddr AddrHalt) $ do
    fail "halt - nothing to do"
  Map.lookup oldStackTop <$> gets sStack >>= \case
    Nothing     -> fail $ "missing stack frame for: " ++ show oldStackTop
    Just frames -> do
      (frame, newStackTop) <- lift . ListT . pure $ Set.toList frames
      modify' $ \s -> s {sStackTop = newStackTop}
      pure frame

{-
  Eval
-}
abstractAtomicEval :: Env -> AExp -> M (Set Clo)
abstractAtomicEval env exp = do
  store <- gets sStore
  case exp of
    Var n -> pure $ store Map.! (env Map.! n)
    Lam{} -> pure $ Set.singleton (exp, env)
    Lit{} -> pure $ Set.singleton (exp, mempty)
    _ -> error $ "unsupported atomic expression: " ++ show exp

abstractEval :: Env -> Exp -> M (Exp, Env)
abstractEval localEnv exp = do
  case exp of
    LetApp (y, f, ae) e -> do
      funValSet <- abstractAtomicEval localEnv f
      (Lam x lamBody, lamEnv) <- lift . ListT . pure $ Set.toList funValSet
      arg <- abstractAtomicEval localEnv ae

      -- HINT: bind arg
      argAddr <- alloc x exp
      extendStore arg argAddr

      stackPush (y, e, localEnv)
      let closureEnv = extendEnv x argAddr lamEnv
      pure (lamBody, closureEnv)

    Let (y, ae) e -> do
      val <- abstractAtomicEval localEnv ae
      valAddr <- alloc y exp
      extendStore val valAddr

      let extendedEnv = extendEnv y valAddr localEnv
      pure (e, extendedEnv)

    ae -> do
      (x, e, env) <- stackPop

      val <- abstractAtomicEval localEnv ae
      valAddr <- alloc x exp
      extendStore val valAddr

      let extendedEnv = extendEnv x valAddr env
      pure (e, extendedEnv)

------------
{-
  Stack machine
-}
type Config = (Exp, Env, KAddr)

workListFixExp :: Exp -> D (Set Config, Store, Stack)
workListFixExp e0 = go mempty mempty [initState] mempty where

  initState :: Config
  initState = (e0, mempty, KAddr AddrHalt)

  storeNotIn :: Store -> Store -> Bool
  storeNotIn small big = not $ Map.isSubmapOfBy Set.isSubsetOf small big

  stackNotIn :: Stack -> Stack -> Bool
  stackNotIn small big = not $ Map.isSubmapOfBy Set.isSubsetOf small big

  go :: Store -> Stack -> [Config] -> Set Config -> D (Set Config, Store, Stack)
  go store stack [] seen = pure (seen, store, stack)
  go store stack ((exp, env, addrK):todo) seen = do
    s <- runListT $ runStateT (abstractEval env exp) (AAMState store stack addrK)
    let storeNext = Map.unionsWith Set.union $ store : [sStore | (_, AAMState{..}) <- s]  -- HINT: store widening
        stackNext = Map.unionsWith Set.union $ stack : [sStack | (_, AAMState{..}) <- s]  -- HINT: stack widening
        new       = [ cfg
                    | ((e, localEnv), AAMState{..}) <- s
                    , let cfg = (e, localEnv, sStackTop)
                    , Set.notMember cfg seen || storeNotIn sStore store || stackNotIn sStack stack
                    ]
        todoNext  = new ++ todo
        seenNext  = Set.union seen $ Set.fromList new
    go storeNext stackNext todoNext seenNext
