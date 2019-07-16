{-# LANGUAGE LambdaCase, RecordWildCards #-}
module Eval where

{-
  interpreter for concrete semantics
-}

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map

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
    done - interpreter
    done - make address allocation monadic (robust)
    - abstract interpreter
  QUESTION:
    - could we map the embedded language to the host language stack instead of the explicit one?
-}
type Addr   = Int
type Lam    = Exp -- Lam constructor only
type Clo    = (Lam, Env)
type Env    = Map Id Addr
type Store  = Map Addr Clo
type Stack  = [(Id, Exp, Env)]

type Alloc = State Addr

alloc :: Alloc Addr
alloc = state $ \i -> (i, succ i)

data P4FState
  = P4FState
  { sEnv      :: Map Id Addr
  , sStore    :: Map Addr Clo
  , sStack    :: [(Id, Exp, Env)]
  }

-- utility
evalAtomic :: Env -> Store -> Exp -> Clo
evalAtomic env store exp = case exp of
  Var n -> store Map.! (env Map.! n)
  Lam{} -> (exp, env)
  _ -> error $ "unsupported expression: " ++ show exp

evalExp :: P4FState -> Exp -> Alloc (Exp, P4FState)
evalExp P4FState{..} = \case
  Let (y, f, ae) e  -> do
    newAddr <- alloc
    let (Lam x e', envLam) = evalAtomic sEnv sStore f
        p4f = P4FState
          { sEnv      = Map.insert x newAddr envLam
          , sStore    = Map.insert newAddr (evalAtomic sEnv sStore ae) sStore
          , sStack    = (y, e, sEnv) : sStack
          }
    pure (e', p4f)

  -- atomic expression
  ae -> do
    newAddr <- alloc
    let (x, e, envKont) : kont = sStack
        p4f = P4FState
          { sEnv      = Map.insert x newAddr envKont
          , sStore    = Map.insert newAddr (evalAtomic sEnv sStore ae) sStore
          , sStack    = kont
          }
    pure (e, p4f)
