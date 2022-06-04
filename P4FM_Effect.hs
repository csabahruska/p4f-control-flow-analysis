{-# LANGUAGE RecordWildCards, LambdaCase, ConstraintKinds #-}
module P4FM_Effect where

import Control.Applicative
import Control.Monad
import Control.Effect.NonDet
import Control.Effect.State
import Control.Effect.Fresh
import Control.Effect.Fail
import Control.Carrier.NonDet.Church
import Control.Carrier.State.Strict
import Control.Carrier.Fail.Either
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
  -- stack section
  , sStack      :: Stack
  , sStackTop   :: KAddr
  }
  deriving (Show, Eq, Ord)

type M sig m =
  ( Has (State AAMState) sig m
  , Has NonDet sig m
  , Has Fail sig m
  , Has Fresh sig m
  , MonadFail m
  , Alternative m
  )

{-
  Env and Store
-}
extendEnv :: Id -> Addr -> Env -> Env
extendEnv var addr env = Map.insert var addr env

extendStore :: M sig m => Set Clo -> Addr -> m ()
extendStore val addr = do
  modify $ \s@AAMState{..} -> s {sStore = Map.insertWith Set.union addr val sStore}

{-
  Allocator
-}
alloc :: M sig m => Id -> Exp -> m Addr
alloc var exp = do
  -- TODO: use the right abstract allocator
  AddrInt <$> fresh

allocK :: M sig m => m KAddr
allocK = do
  -- TODO: use the right abstract allocator
  KAddr . AddrInt <$> fresh

{-
  Stack
-}
stackPush :: M sig m => Frame -> m ()
stackPush frame = do
  newStackTop <- allocK -- TODO: add access to the necessary information
  oldStackTop <- gets sStackTop
  let frameContinuation = Set.singleton (frame, oldStackTop)
  modify $ \s@AAMState{..} -> s
    { sStack    = Map.insertWith Set.union newStackTop frameContinuation sStack
    , sStackTop = newStackTop
    }

stackPop :: M sig m =>m Frame
stackPop = do
  oldStackTop <- gets sStackTop
  when (oldStackTop == KAddr AddrHalt) $ do
    fail "halt - nothing to do"
  Map.lookup oldStackTop <$> gets sStack >>= \case
    Nothing     -> fail $ "missing stack frame for: " ++ show oldStackTop
    Just frames -> do
      (frame, newStackTop) <- oneOf $ Set.toList frames
      modify $ \s -> s {sStackTop = newStackTop}
      pure frame

{-
  Eval
-}

abstractAtomicEval :: M sig m => Env -> AExp -> m (Set Clo)
abstractAtomicEval localEnv exp = do
  store <- gets sStore
  case exp of
    Var n -> pure $ store Map.! (localEnv Map.! n)
    Lam{} -> pure $ Set.singleton (exp, localEnv)
    Lit{} -> pure $ Set.singleton (exp, mempty)
    _ -> error $ "unsupported atomic expression: " ++ show exp


abstractEval :: M sig m => Env -> Exp -> m (Exp, Env)
abstractEval localEnv exp = do
  case exp of
    LetApp (y, f, ae) e -> do
      funValSet <- abstractAtomicEval localEnv f
      (Lam x lamBody, lamEnv) <- oneOf $ Set.toList funValSet
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
      -- lookup atomic value
      val <- abstractAtomicEval localEnv ae

      -- bind the return value to a variable in caller's environment
      (x, e, callerEnv) <- stackPop

      valAddr <- alloc x exp
      extendStore val valAddr
      let extendedEnv = extendEnv x valAddr callerEnv
      pure (e, extendedEnv)

------------
{-
  Stack machine
-}
type Config = (Exp, Env, KAddr)

storeNotIn :: Store -> Store -> Bool
storeNotIn small big = not $ Map.isSubmapOfBy Set.isSubsetOf small big

stackNotIn :: Stack -> Stack -> Bool
stackNotIn small big = not $ Map.isSubmapOfBy Set.isSubsetOf small big

workListFixExp :: Has Fresh sig m => Exp -> m (Set Config, Store, Stack)
workListFixExp e0 = go mempty mempty [initState] mempty where

  initState :: Config
  initState = (e0, mempty, KAddr AddrHalt)

  go :: Has Fresh sig m => Store -> Stack -> [Config] -> Set Config -> m (Set Config, Store, Stack)
  go store stack [] seen = pure (seen, store, stack)
  go store stack ((exp, env, addrK):todo) seen = do
    s <- runNonDetA $ runFail $ flip runState (abstractEval env exp) (AAMState store stack addrK)
    let storeNext = Map.unionsWith Set.union $ store : [sStore | Right (AAMState{..}, _) <- s]  -- HINT: store widening
        stackNext = Map.unionsWith Set.union $ stack : [sStack | Right (AAMState{..}, _) <- s]  -- HINT: stack widening
        new       = [ cfg
                    | Right (AAMState{..}, (e, localEnv)) <- s
                    , let cfg = (e, localEnv, sStackTop)
                    , Set.notMember cfg seen || storeNotIn sStore store || stackNotIn sStack stack
                    ]
        todoNext  = new ++ todo
        seenNext  = Set.union seen $ Set.fromList new
    go storeNext stackNext todoNext seenNext

{-
  To think about:
    - empty stack, machine termination
    - non-determinism (eval vs atomic-eval)
    - value allocation on store, can it be an atomic operation and be hidden by a utility function?
    - how to return the final value of the evaluation?
-}
