{-# LANGUAGE LambdaCase, RecordWildCards, TupleSections #-}
module TestP4FM_Effect where

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Text.Show.Pretty

import Control.Carrier.Fresh.Strict

--import P4FM
import P4FM_Effect

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

test :: Exp -> IO String
test exp = do
  let result = run $ evalFresh 0 (workListFixExp exp)
  let (c,s,k) = simplifyAddr result
  pure $ ppShow ("Config", c, "Store", s, "Stack", k)

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
