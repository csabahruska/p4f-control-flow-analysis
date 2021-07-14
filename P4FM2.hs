{-# LANGUAGE RecordWildCards, LambdaCase #-}
module P4FM2 where

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

-- Program point descriptor
type ProgramPoint = (Env, Exp) -- HINT: for allocK and P4F

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
  -- stack section
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
  --lift . lift . state $ \i -> (AddrInt i, succ i)
  -- 1-CFA
  pure $ AddrIdExp var exp

allocK :: (Env, Exp) -> M KAddr
allocK (env, exp) = do
  -- TODO: use the right abstract allocator
  --lift . lift . state $ \i -> (KAddr $ AddrInt i, succ i)
  -- P4F
  pure . KAddr $ AddrExpEnv exp env

{-
  Stack
-}
stackPush :: ProgramPoint -> Frame -> M ()
stackPush progPoint frame = do
  newStackTop <- allocK progPoint
  oldStackTop <- gets sStackTop
  let frameContinuation = Set.singleton (frame, oldStackTop)
  modify' $ \s@AAMState{..} -> s
    { sStack    = Map.insertWith Set.union newStackTop frameContinuation sStack
    , sStackTop = newStackTop
    }

stackPop :: M (Maybe Frame)
stackPop = do
  oldStackTop <- gets sStackTop
  case oldStackTop of
    KAddr AddrHalt -> pure Nothing
    _ -> Map.lookup oldStackTop <$> gets sStack >>= \case
      Nothing     -> fail $ "missing stack frame for: " ++ show oldStackTop
      Just frames -> do
        (frame, newStackTop) <- lift . ListT . pure $ Set.toList frames
        modify' $ \s -> s {sStackTop = newStackTop}
        pure $ Just frame

{-
  Eval
-}
abstractAtomicEval :: Env -> AExp -> M (Set Clo)
abstractAtomicEval localEnv exp = do
  store <- gets sStore
  case exp of
    Var n -> pure $ store Map.! (localEnv Map.! n)
    Lam{} -> pure $ Set.singleton (exp, localEnv)
    Lit{} -> pure $ Set.singleton (exp, mempty)
    _ -> error $ "unsupported atomic expression: " ++ show exp

data BindContinuation
  = Next    Exp Env
  | Result  Exp Env (Set Clo) -- HINT: result value

abstractEval :: Env -> Exp -> M BindContinuation
abstractEval localEnv exp = do
  case exp of
    LetApp (y, f, ae) e -> do
      funValSet <- abstractAtomicEval localEnv f
      (Lam x lamBody, lamEnv) <- lift . ListT . pure $ Set.toList funValSet
      arg <- abstractAtomicEval localEnv ae

      -- HINT: bind arg
      argAddr <- alloc x exp  -- HINT: caller point + local point (from the stack top point of view after the closure has entered)
      extendStore arg argAddr

      let closureEnv  = extendEnv x argAddr lamEnv
          progPoint   = (closureEnv, lamBody)
      stackPush progPoint (y, e, localEnv)
      pure $ Next lamBody closureEnv
{-
    Let (y, ae) e -> do
      val <- abstractAtomicEval localEnv ae
      valAddr <- alloc y exp -- HINT: local program point ; this is WRONG because it is not 1-CFA value allocator
      extendStore val valAddr

      let extendedEnv = extendEnv y valAddr localEnv
      pure $ Next e extendedEnv
-}
    ae -> do
      -- lookup atomic value
      val <- abstractAtomicEval localEnv ae

      -- bind the return value to a variable in caller's environment
      stackPop >>= \case
        Nothing -> pure $ Result exp localEnv val
        Just (x, e, callerEnv) -> do
          valAddr <- alloc x exp  -- HINT: caller point + local point (before the closure returns ; point of view)
          extendStore val valAddr
          let extendedEnv = extendEnv x valAddr callerEnv
          pure $ Next e extendedEnv

------------
{-
  Stack machine
-}
type Config = (Exp, Env, KAddr)
type Result = (Exp, Env, Set Clo)

storeNotIn :: Store -> Store -> Bool
storeNotIn small big = not $ Map.isSubmapOfBy Set.isSubsetOf small big

stackNotIn :: Stack -> Stack -> Bool
stackNotIn small big = not $ Map.isSubmapOfBy Set.isSubsetOf small big

workListFixExp :: Exp -> D (Set Config, Store, Stack)
workListFixExp e0 = go mempty mempty [initState] mempty mempty where

  initState :: Config
  initState = (e0, mempty, KAddr AddrHalt)

  go :: Store -> Stack -> [Config] -> Set Config -> Set Result -> D (Set Config, Store, Stack)
  go store stack [] seen results = pure (seen, store, stack)
  go store stack ((exp, env, addrK):todo) seen results = do
    s <- runListT $ runStateT (abstractEval env exp) (AAMState store stack addrK)
    let storeNext = Map.unionsWith Set.union $ store : [sStore | (_, AAMState{..}) <- s]  -- HINT: store widening
        stackNext = Map.unionsWith Set.union $ stack : [sStack | (_, AAMState{..}) <- s]  -- HINT: stack widening
        new       = [ cfg
                    | (Next e localEnv, AAMState{..}) <- s -- TODO: handle Result also ; collect final states + values
                    , let cfg = (e, localEnv, sStackTop)
                    , Set.notMember cfg seen || storeNotIn sStore store || stackNotIn sStack stack
                    ]
        todoNext  = new ++ todo
        seenNext  = Set.union seen $ Set.fromList new
        resultsNext = Set.unions $ results : [Set.singleton (e, localEnv, valSet) | (Result e localEnv valSet, _) <- s]
    go storeNext stackNext todoNext seenNext resultsNext
{-
  To think about:
    done - empty stack, machine termination
    done - how to return the final value of the evaluation?
    - non-determinism (eval vs atomic-eval)
    - value allocation on store, can it be an atomic operation and be hidden by a utility function?
-}
