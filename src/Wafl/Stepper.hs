{-# language ViewPatterns #-}
module Wafl.Stepper where

import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Reader

import Data.Foldable (traverse_)

import Unbound.Generics.LocallyNameless.Operations (unrebind, unrec, unbind, unembed)
import Unbound.Generics.LocallyNameless.Fresh (Fresh)

import Wafl.Syntax

type Assoc a b = [(a,b)]

type GlobalEnv = Assoc FVar Function

type FunEnv = (Assoc CVar Continuation, CVar) -- lconts, retk

type LocalEnv = (Assoc Variable Value, (LVar, [Value]))

type ResidualProgram = Decls

data GlobalCmd = NextDecl
               | EvalResult Value
               | Eval FunEnv FunCmd [FunFrame]
               deriving (Show)

data FunCmd = Ret Value
            | Jmp CVar Value [Value]
            | Step LocalEnv Term
            deriving (Show)

data FunFrame = FunFrame FunEnv CVar [Value]
  deriving (Show)

data Result = Done
            | ErrUnboundFn FVar
            | ErrUnboundK CVar
            | ErrUnboundLV LVar
            | ErrUnboundVariable Variable
            | ErrStackNotEmpty
            | ErrWrongOperands Op
            deriving (Show)

initial :: Fresh m => Program -> m (GlobalCmd, ResidualProgram)
initial (Program bnd) =
  unbind bnd >>= \(ds, ()) -> return (NextDecl, ds)

step :: Fresh m => GlobalCmd -> ResidualProgram
  -> ExceptT Result (StateT GlobalEnv m) (GlobalCmd, ResidualProgram)
step cmd_ p =
  case cmd_ of
    NextDecl -> case p of
      NilDecls -> throwError Done
      ConsDecls (unrebind -> (dg, p')) -> do
        cmd <- case dg of
          SingleDecl (PragmaDecl pg) -> enterPragma pg
          SingleDecl (SimpleDecl d) -> addDecl d >> return NextDecl
          RecDecl (RecDecls (unrec -> ds)) -> traverse_ addDecl ds >> return NextDecl
        return (cmd, p')
    EvalResult _val ->
      return (NextDecl, p)
    Eval fenv cmd fs -> do
      cmd' <- enterEval fenv cmd fs
      return (cmd', p)

addDecl :: Fresh m => Decl -> ExceptT Result (StateT GlobalEnv m) ()
addDecl d = case d of
  FunDecl (FnDefn (unrebind -> (f, unembed -> fct))) ->
    modify ((f,fct):)
  

enterPragma :: Fresh m => Pragma -> ExceptT Result (StateT GlobalEnv m) GlobalCmd
enterPragma pg =
  case pg of
    InfoPragma {} -> return NextDecl
    EvalPragma (unembed -> (f, v)) -> enterFunction f v

enterFunction :: Fresh m => FVar -> Value ->
  ExceptT Result (StateT GlobalEnv m) GlobalCmd
enterFunction f v = do
  m <- gets (lookup f)
  case m of
    Nothing -> throwError (ErrUnboundFn f)
    Just (Function bnd) -> do
      (kret, FnBody bodybnd) <- unbind bnd
      (ContDefs (unrec -> conts), kenter) <- unbind bodybnd
      let funEnv = (map mkContEnv conts, kret)
      return $ Eval funEnv (Jmp kenter v []) []
        
mkContEnv :: ContDef -> (CVar, Continuation)
mkContEnv (ContDef (unrebind -> (k, unembed -> continuation))) = (k, continuation)

enterEval :: Fresh m
          => FunEnv -> FunCmd -> [FunFrame]
          -> ExceptT Result (StateT GlobalEnv m) GlobalCmd
enterEval fenv cmd fs =
  case (cmd, fs) of
    (Ret v, []) -> return (EvalResult v)
    _ -> do
      g <- get
      res <- lift $ lift $ flip runReaderT g $ runExceptT $ stepLocal fenv cmd fs
      case res of
        Left err -> throwError err
        Right (fenv', cmd', fs') -> return (Eval fenv' cmd' fs')


stepLocal :: Fresh m
  => FunEnv -> FunCmd -> [FunFrame]
  -> ExceptT Result (ReaderT GlobalEnv m) (FunEnv, FunCmd, [FunFrame])
stepLocal _fenv (Ret _v) [] = error "unexpected stepLocal return with empty frames"
stepLocal _fenv (Ret v) (FunFrame fenv k stk : fs) =
  return (fenv, Jmp k v stk, fs)
stepLocal fenv (Jmp k v stk) fs =
  if (snd fenv) == k
  then do
    case stk of
      [] -> return (fenv, Ret v, fs)
      _ -> throwError ErrStackNotEmpty
  else case lookup k (fst fenv) of
    Nothing -> throwError (ErrUnboundK k)
    Just (Continuation bnd) -> do
      ((x, l), m) <- unbind bnd
      let lenv = ([(x, v)], (l, stk))
      return (fenv, Step lenv m, fs)
stepLocal fenv (Step lenv (Jump k v lv)) fs = do
  stk <- evalLValue lenv lv
  v' <- evalValue lenv v
  return (fenv, Jmp k v' stk, fs)
stepLocal fenv (Step lenv (Call f v lv k)) fs = do
  stk <- evalLValue lenv lv
  v' <- evalValue lenv v
  m <- asks (lookup f)
  case m of
    Nothing -> throwError (ErrUnboundFn f)
    Just (Function bnd) -> do
      let f' = FunFrame fenv k stk
      (kret, FnBody bodybnd) <- unbind bnd
      (ContDefs (unrec -> conts), kenter) <- unbind bodybnd
      let fenv' = (map mkContEnv conts, kret)
      return (fenv', Jmp kenter v' [], f':fs)
stepLocal fenv (Step lenv (LetE e bnd)) fs = do
  (x, m) <- unbind bnd
  v <- evalExpr lenv e
  let lenv' = addLocal x v lenv
  return (fenv, Step lenv' m, fs)
stepLocal _fenv _ _fs = error "finish stepLocal"

addLocal :: Variable -> Value -> LocalEnv -> LocalEnv
addLocal x v (bs, lin) = ((x,v):bs, lin)

evalExpr :: Monad m => LocalEnv -> Expr -> ExceptT Result m Value
evalExpr lenv e =
  case e of
    EValue v -> evalValue lenv v
    EOp op vs -> do
      vs' <- traverse (evalValue lenv) vs
      case (op, vs') of
        (Add, [IntV n1, IntV n2]) -> return (IntV $! n1 + n2)
        _ -> throwError (ErrWrongOperands op)

evalValue :: Monad m => LocalEnv -> Value -> ExceptT Result m Value
evalValue lenv v =
  case v of
    IntV {} -> return v
    UnitV -> return v
    VarV x -> case lookup x (fst lenv) of
      Nothing -> throwError (ErrUnboundVariable x)
      Just v' -> return v'

evalLValue :: Monad m => LocalEnv -> LinearValue -> ExceptT Result m [Value]
evalLValue lenv lv =
   case (lenv, lv) of
     ((_vs, (l, stk)), VarLV l') ->
       if l == l'
       then return stk
       else throwError (ErrUnboundLV l')
