{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
module Prob where

import Control.Applicative
import Control.Error
import Control.Lens.Combinators
import Control.Monad.ST
import Control.Monad.State
import Data.Bifunctor
import Data.List
import qualified Data.Map.Strict as M
import Data.String
import System.Random.MWC
import System.Random.MWC.Distributions
import Text.Groom

data Expr varTy
  = Var varTy
  | Constant Double
  | Plus (Expr varTy)
         (Expr varTy)
  | Minus (Expr varTy)
          (Expr varTy)
  | Mult (Expr varTy)
         (Expr varTy)
  | Div (Expr varTy)
        (Expr varTy)
  | Abs (Expr varTy)
  | And (Expr varTy)
        (Expr varTy)
  | Or (Expr varTy)
       (Expr varTy)
  | Not (Expr varTy)
  | Eq (Expr varTy) (Expr varTy)
  deriving (Show, Functor, Foldable, Traversable)

data Dist varTy
  = Normal (Expr varTy)
           (Expr varTy)
  | Exponential (Expr varTy)
  | Geometric (Expr varTy)
  | Bernoulli (Expr varTy)
  deriving (Show, Functor, Foldable, Traversable)

infix 1 :=

infix 1 :~

infixr 0 `Seq`

newtype Then varTy =
  Then (Stmt varTy)
  deriving (Show, Functor, Foldable, Traversable)

newtype Else varTy =
  Else (Stmt varTy)
  deriving (Show, Functor, Foldable, Traversable)

data Stmt varTy
  = Skip
  | varTy := (Expr varTy)
  | varTy :~ (Dist varTy)
  | Observe (Expr varTy)
  | Seq (Stmt varTy)
        (Stmt varTy)
  | If (Expr varTy)
       (Then varTy)
       (Else varTy)
  | While (Expr varTy)
          (Stmt varTy)
  deriving (Show, Functor, Foldable, Traversable)

data Prog varTy =
  Return (Stmt varTy)
         (Expr varTy)
  deriving (Show, Functor, Foldable, Traversable)

--------------------------------------------------------------------------------
-- Instances & Syntactic Sugar in our host language
--------------------------------------------------------------------------------
$(makePrisms ''Expr)
$(makePrisms ''Dist)
$(makePrisms ''Stmt)
$(makePrisms ''Prog)

instance Num (Expr vt) where
  (+) = Plus
  (-) = Minus
  (*) = Mult
  abs = Abs
  signum = error "unsupported operation"
  fromInteger = Constant . fromInteger

instance Fractional (Expr vt) where
  fromRational = Constant . fromRational
  (/) = Div

instance IsString (Expr String) where
  fromString = Var

instance Plated (Expr varTy) where
  plate f (Plus e1 e2) = Plus <$> f e1 <*> f e2
  plate f (Minus e1 e2) = Minus <$> f e1 <*> f e2
  plate f (Mult e1 e2) = Mult <$> f e1 <*> f e2
  plate f (Div e1 e2) = Div <$> f e1 <*> f e2
  plate f (And e1 e2) = And <$> f e1 <*> f e2
  plate f (Or e1 e2) = Or <$> f e1 <*> f e2
  plate f (Eq e1 e2) = Eq <$> f e1 <*> f e2
  plate f (Abs e) = Abs <$> f e
  plate f (Not e) = Not <$> f e
  plate _ s = pure s

instance Plated (Stmt varTy) where
  plate f (Seq s1 s2) = Seq <$> f s1 <*> f s2
  plate f (If c (Then t) (Else e)) = If c <$> (Then <$> f t) <*> (Else <$> f e)
  plate f (While e s) = While e <$> f s
  plate _ s = pure s

--------------------------------------------------------------------------------
-- | The program state consists of a list of variable assignments and the state
-- of the random number generator. All variables are global variables.
type ProgState vt s = ([(vt, Double)], Gen s)

-- | The evaluation monad.
type Eval vt s = MaybeT (StateT (ProgState vt s) (ST s))

runE :: Eval vt s a -> IO (Maybe a)
runE e = withSystemRandom . asGenST $ (\rng -> evalStateT (runMaybeT e) ([], rng))

runEs :: Int -> Eval vt s a -> IO [a]
runEs t e = withSystemRandom . asGenST $ (\rng -> catMaybes <$> evalStateT (replicateM t (runMaybeT e)) ([], rng))

evalExpr :: (Show vt, Ord vt) => Expr vt -> Eval vt s Double
evalExpr (Var x) = fromMaybe (error $ "undefined variable " ++ show x) <$> gets (lookup x . fst)
evalExpr (Constant d) = pure d
evalExpr (Plus a b) = liftA2 (+) (evalExpr a) (evalExpr b)
evalExpr (Minus a b) = liftA2 (-) (evalExpr a) (evalExpr b)
evalExpr (Mult a b) = liftA2 (*) (evalExpr a) (evalExpr b)
evalExpr (Div a b) = liftA2 (/) (evalExpr a) (evalExpr b)
evalExpr (Abs a) = abs <$> evalExpr a
evalExpr (Or a b) = boolToDouble <$> liftA2 (||) (doubleToBool <$> evalExpr a) (doubleToBool <$> evalExpr b)
evalExpr (And a b) = boolToDouble <$> liftA2 (&&) (doubleToBool <$> evalExpr a) (doubleToBool <$> evalExpr b)
evalExpr (Not a) = boolToDouble . not . doubleToBool <$> evalExpr a
evalExpr (Eq a b) = boolToDouble <$> liftA2 (==) (evalExpr a) (evalExpr b)

doubleToBool :: Double -> Bool
doubleToBool x = not (x == 0 || isNaN x)

boolToDouble :: Bool -> Double
boolToDouble = bool 0.0 1.0

drawDist :: (Show vt, Ord vt) => Dist vt -> Eval vt s Double
drawDist (Normal m sd) = do
  m' <- evalExpr m
  sd' <- evalExpr sd
  rng <- gets snd
  lift (normal m' sd' rng)
drawDist (Exponential s) = do
  s' <- evalExpr s
  rng <- gets snd
  lift (exponential s' rng)
drawDist (Geometric p) = do
  p' <- evalExpr p
  rng <- gets snd
  lift (fromIntegral <$> geometric0 p' rng)
drawDist (Bernoulli p) = do
  p' <- evalExpr p
  rng <- gets snd
  lift (boolToDouble <$> bernoulli p' rng)

evalStmt :: (Show vt, Ord vt) => Stmt vt -> Eval vt s ()
evalStmt Skip = pure ()
evalStmt (x := a) = do
  v <- evalExpr a
  modify (first ((x, v) :))
evalStmt (x :~ d) = do
  v <- drawDist d
  modify (first ((x, v) :))
evalStmt (Observe e) = do
  e' <- evalExpr e
  if doubleToBool e'
    then pure ()
    else MaybeT $ pure Nothing
evalStmt (Seq a b) = evalStmt a >> evalStmt b
evalStmt (If e (Then thenn) (Else alt)) = do
  e' <- evalExpr e
  if doubleToBool e'
    then evalStmt thenn
    else evalStmt alt
evalStmt s@(While e stmt) = do
  e' <- evalExpr e
  if doubleToBool e'
    then evalStmt stmt >> evalStmt s
    else pure ()

evalProg :: (Show vt, Ord vt) => Prog vt -> Eval vt s Double
evalProg (Return stmt expr) = evalStmt stmt >> evalExpr expr

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------
-- | Crude pretty printer
pr :: Show a => a -> IO ()
pr = putStrLn . groom

tally :: Ord a => [a] -> [(a, Int)]
tally = map (liftA2 (,) head length) . group . sort

--------------------------------------------------------------------------------
-- Example Programs
--------------------------------------------------------------------------------
stmt1 :: Stmt String
stmt1 = "a" := 1 `Seq` If "a" (Then $ "b" := 1) (Else $ "b" := 0)

stmt2 :: Stmt String
stmt2 = "a" := 1 `Seq` "a" := "a" + 1

example1 :: Prog String
example1 =
  ("count" := 0 `Seq`
   "c1" :~ Bernoulli 0.5 `Seq`
   If "c1" (Then ("count" := "count" + 1)) (Else Skip) `Seq`
   "c2" :~ Bernoulli 0.5 `Seq` If "c2" (Then ("count" := "count" + 1)) (Else Skip)) `Return`
  "count"

example2 :: Prog String
example2 =
  ("count" := 0 `Seq`
   "c1" :~ Bernoulli 0.5 `Seq`
   If "c1" (Then ("count" := "count" + 1)) (Else Skip) `Seq`
   "c2" :~ Bernoulli 0.5 `Seq` If "c2" (Then ("count" := "count" + 1)) (Else Skip) `Seq` Observe ("c1" `Or` "c2")) `Return`
  "count"

example3 :: Prog String
example3 =
  ("d" :~ Bernoulli 0.6 `Seq`
   "i" :~ Bernoulli 0.7 `Seq`
   If
     (Not "i" `And` Not "d")
     (Then ("g" :~ Bernoulli 0.3))
     (Else
        (If
           (Not "i" `And` "d")
           (Then ("g" :~ Bernoulli 0.05))
           (Else (If ("i" `And` Not "d") (Then ("g" :~ Bernoulli 0.9)) (Else ("g" :~ Bernoulli 0.5)))))) `Seq`
   If (Not "i") (Then ("s" :~ Bernoulli 0.2)) (Else ("s" :~ Bernoulli 0.95)) `Seq`
   If (Not "g") (Then ("l" :~ Bernoulli 0.1)) (Else ("l" :~ Bernoulli 0.4))) `Return`
  "s"

--------------------------------------------------------------------------------
-- Generic Simplify
--------------------------------------------------------------------------------
basicSimplification :: Stmt vt -> Stmt vt
basicSimplification = rewrite f
  where f (Seq (Seq s1 s2) s3) = Just (Seq s1 (Seq s2 s3)) -- associate Seq to the right
        f (Seq a Skip) = Just a
        f (Seq Skip a) = Just a
        f _ = Nothing

noVariables :: Expr vt -> Bool
noVariables = hasn't (cosmos . _Var)

obs :: Prog vt -> Prog vt
obs (Return stmt rv) = Return (rewrite f stmt) rv
  where f s@(Observe (Var x `Eq` e)) = Just (Seq s (x := e))
        f s@(Observe (e `Eq` Var x)) = Just (Seq s (x := e))
        f s@(While (Not (Var x `Eq` e)) _) = Just (Seq s (x := e))
        f s@(While (Not (e `Eq` Var x)) _) = Just (Seq s (x := e))
        f _ = Nothing


--------------------------------------------------------------------------------
-- Rename variables into numbers
--------------------------------------------------------------------------------
-- | We need to keep track of the next number and the variable mappings.
type RenamerState vt = (Int, M.Map vt Int)

type Renamer vt a = State (RenamerState vt) a

fresh :: Renamer vt Int
fresh = state (\s -> (fst s, first (+1) s))

addMapping :: (Ord vt) => Int -> vt -> Renamer vt ()
addMapping i x = modify' (second (M.insert x i))

renamer :: (Ord vt, Traversable f) => f vt -> Renamer vt (f Int)
renamer = traverse f
  where f vt = gets snd >>= \m -> case M.lookup vt m of
          Just i -> pure i
          Nothing -> do
            i <- fresh
            addMapping i vt
            pure i

rename :: (Ord vt) => Prog vt -> Prog Int
rename prog = evalState (renamer prog) (1, M.empty)

--------------------------------------------------------------------------------
-- Single Variable Form
--------------------------------------------------------------------------------
type SVF a = State Int a

fresh' :: SVF Int
fresh' = state (\i -> (i, i+1))

doSvf :: Stmt vt -> SVF (Stmt (Either Int vt))
doSvf (Observe (Var x)) = pure (Observe (Var (Right x)))
doSvf (Observe e) = do
  i <- fresh'
  pure (Seq (Left i := Right <$> e) (Observe (Var (Left i))))
doSvf (While (Var x) l) = pure (While (Var (Right x)) (Right <$> l))
doSvf (While e l) = do
  i <- fresh'
  pure (Seq (Left i := Right <$> e) (While (Var (Left i)) (Right <$> l)))
doSvf (Seq s1 s2) = Seq <$> doSvf s1 <*> doSvf s2
doSvf (If (Var c) (Then t) (Else e)) = If (Var (Right c)) <$> (Then <$> doSvf t) <*> (Else <$> doSvf e)
doSvf (If c (Then t) (Else e)) = do
  i <- fresh'
  t' <- doSvf t
  e' <- doSvf e
  pure (Seq (Left i := Right <$> c) (If (Var (Left i)) (Then t') (Else e')))
doSvf s = pure (Right <$> s)

svf :: Prog vt -> Prog (Either Int vt)
svf (Return s e) = evalState (Return <$> doSvf s <*> pure (Right <$> e)) 1

--------------------------------------------------------------------------------
-- SSA
--------------------------------------------------------------------------------

-- | While performing SSA, we need to keep track of the next number and the
-- variable mappings.
type SSATransformState vt = (Int, M.Map vt Int)

type SSA vt a = State (SSATransformState vt) a

freshVar :: SSA vt Int
freshVar = state (\s -> (fst s, first (+1) s))

addVarMap :: (Ord vt) => Int -> vt -> SSA vt ()
addVarMap i x = modify' (second (M.insert x i))

replaceAll :: (Ord vt, Show vt, Functor f) => f vt -> SSA vt (f Int)
replaceAll stmt = do
  currentMap <- gets snd
  pure ((\var -> fromMaybe (error $ "undefined variable " ++ show var) (M.lookup var currentMap)) <$> stmt)

merge :: (Show vt, Ord vt) => SSA vt a -> SSA vt b -> SSA vt (a, b, Stmt Int)
merge ssa1 ssa2 =
  StateT $ \s ->
    let (s1', (x', rho')) = runState ssa1 s
        (s2', (x'', rho'')) = runState ssa2 (first (const x') s)
    in Identity ((s1', s2', mergeRec rho' rho''), (x'', rho'))
  where
    mergeRec :: (Show vt, Ord vt) => M.Map vt Int -> M.Map vt Int -> Stmt Int
    mergeRec rho rho' =
      foldr
        (\vt stmt ->
           case (M.lookup vt rho, M.lookup vt rho') of
             (Just i1, Just i2)
               | i1 /= i2 -> Seq (i1 := Var i2) stmt
             _ -> stmt)
        Skip
        (M.keys rho)

doSSA :: (Show vt, Ord vt) => Stmt vt -> SSA vt (Stmt Int)
doSSA Skip = pure Skip
doSSA s@(Observe _) = replaceAll s
doSSA (x := e) = do
  i <- freshVar
  e' <- replaceAll e
  addVarMap i x
  pure (i := e')
doSSA (x :~ e) = do
  i <- freshVar
  e' <- replaceAll e
  addVarMap i x
  pure (i :~ e')
doSSA (Seq s1 s2) = do
  s1' <- doSSA s1
  s2' <- doSSA s2
  pure (Seq s1' s2')
doSSA (If c (Then s1) (Else s2)) = do
  (s1', s2', s2'') <- merge (doSSA s1) (doSSA s2)
  c' <- replaceAll c
  pure (If c' (Then s1') (Else (Seq s2' s2'')))
doSSA (While e s) = do
  ((), s', s'') <- merge (pure ()) (doSSA s)
  e' <- replaceAll e
  pure (While e' (Seq s' s''))

doSSAProg :: (Show vt, Ord vt) => Prog vt -> SSA vt (Prog Int)
doSSAProg (s `Return` e) = do
  s' <- doSSA s
  e' <- replaceAll e
  pure (basicSimplification s' `Return` e')

ssaStmt :: (Show vt, Ord vt) => Stmt vt -> Stmt Int
ssaStmt stmt = basicSimplification (evalState (doSSA stmt) (1, M.empty))

ssa :: (Show vt, Ord vt) => Prog vt -> Prog Int
ssa prog = evalState (doSSAProg prog) (1, M.empty)
