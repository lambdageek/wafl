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
               | PragmaAnswer EvalRes
               | Eval EvalStep
               deriving (Show)

data EvalStep = EvalAns FunRes [FunFrame]
             | EvalFun FunStep [FunFrame]
             deriving (Show)

data EvalRes = EvalResult Value
             deriving (Show)

data FunStep = FunStep FunEnv LocalStep
             | FunAns FunEnv LocalRes
             deriving (Show)

data FunRes = FunRet Value
             | FunCall FVar Value FunFrame
            deriving (Show)

data LocalStep = Step LocalEnv Term
              | Jmp CVar Value [Value]
            deriving (Show)

data LocalRes = Ret Value
              | LocalCall FVar Value LocalFrame
              deriving (Show)

data FunFrame = FunFrame FunEnv LocalFrame
              deriving (Show)

data LocalFrame = LocalFrame CVar [Value]
                deriving (Show)

data Result = Done
            | ErrUnboundFn FVar
            | ErrUnboundK CVar
            | ErrUnboundLV LVar
            | ErrUnboundVariable Variable
            | ErrStackNotEmpty
            | ErrWrongOperands Op
            | ErrWrongCompare Cmp
            | ErrUnexpectedEmptyStack LinearValue
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
          SingleDecl (PragmaDecl pg) -> mapExceptT readonlyGlobalEnv (enterPragma pg)
          SingleDecl (SimpleDecl d) -> addDecl d >> return NextDecl
          RecDecl (RecDecls (unrec -> ds)) -> traverse_ addDecl ds >> return NextDecl
        return (cmd, p')
    PragmaAnswer _result -> return (NextDecl, p)
    Eval estep -> do
      x <- mapExceptT readonlyGlobalEnv (stepEvalStep estep)
      case x of
        Left res -> return (PragmaAnswer res, p)
        Right estep' -> return (Eval estep', p)

stepEvalStep :: Fresh m => EvalStep -> ExceptT Result (ReaderT GlobalEnv m) (Either EvalRes EvalStep)
stepEvalStep ec_ =
  case ec_ of
    EvalAns res fs_ ->
      case (res, fs_) of
        (FunRet v, []) -> return (Left $ EvalResult v)
        (FunRet v, FunFrame fenv (LocalFrame k stk) : fs) -> do
          return (Right $ EvalFun (FunStep fenv (Jmp k v stk)) fs)
        (FunCall f v frame, fs) -> do
          fcmd' <- enterFunCall f v
          return (Right $ EvalFun fcmd' (frame:fs))
    EvalFun fcmd fs -> do
      x <- stepFunStep fcmd
      case x of
        Left res -> return (Right $ EvalAns res fs)
        Right stp -> return (Right $ EvalFun stp fs)

readonlyGlobalEnv :: Monad m => ReaderT g m a -> StateT g m a
readonlyGlobalEnv comp = do
  g <- get
  lift $ runReaderT comp g

addDecl :: Fresh m => Decl -> ExceptT Result (StateT GlobalEnv m) ()
addDecl d = case d of
  FunDecl (FnDefn (unrebind -> (f, unembed -> fct))) ->
    modify ((f,fct):)

enterPragma :: Fresh m => Pragma -> ExceptT Result (ReaderT GlobalEnv m) GlobalCmd
enterPragma pg =
  case pg of
    InfoPragma {} -> return NextDecl
    EvalPragma (unembed -> (f, v)) -> do
      fstp <- enterFunCall f v
      return (Eval (EvalFun fstp []))

mkContEnv :: ContDef -> (CVar, Continuation)
mkContEnv (ContDef (unrebind -> (k, unembed -> continuation))) = (k, continuation)

stepFunStep :: Fresh m
          => FunStep
          -> ExceptT Result (ReaderT GlobalEnv m) (Either FunRes FunStep)
stepFunStep fcmd_ =
  case fcmd_ of
    FunAns fenv (LocalCall f v lf) -> do
        let f' = FunFrame fenv lf
        return (Left (FunCall f v f'))
    FunAns _fenv (Ret v) -> return (Left (FunRet v))
    FunStep fenv stp -> do
      x <- mapExceptT (inEnvironment fenv) (stepLocal stp)
      case x of
        Left ans -> return (Right (FunAns fenv ans))
        Right stp' -> return (Right (FunStep fenv stp'))

enterFunCall :: Fresh m
             => FVar -> Value -> ExceptT Result (ReaderT GlobalEnv m) FunStep
enterFunCall f v = do
  m <- asks (lookup f)
  case m of
    Nothing -> throwError (ErrUnboundFn f)
    Just (Function bnd) -> do
      (kret, FnBody bodybnd) <- unbind bnd
      (ContDefs (unrec -> conts), kenter) <- unbind bodybnd
      let fenv' = (map mkContEnv conts, kret)
      return (FunStep fenv' (Jmp kenter v []))

stepLocal :: Fresh m
  => LocalStep
  -> ExceptT Result (ReaderT FunEnv m) (Either LocalRes LocalStep)
stepLocal (Jmp k v stk) = enterJmp k v stk
stepLocal (Step lenv m) = mapExceptT (inEnvironment lenv) (stepTerm m)

enterJmp :: Fresh m
  => CVar -> Value -> [Value]
  -> ExceptT Result (ReaderT FunEnv m) (Either LocalRes LocalStep)
enterJmp k v stk = do
  (conts, kret) <- ask
  if kret == k
  then do
    case stk of
      [] -> return (Left $ Ret v)
      _ -> throwError ErrStackNotEmpty
  else case lookup k conts of
    Nothing -> throwError (ErrUnboundK k)
    Just (Continuation bnd) -> do
      ((x, l), m) <- unbind bnd
      let lenv = ([(x, v)], (l, stk))
      return (Right $ Step lenv m)

addLocal :: Variable -> Value -> LocalEnv -> LocalEnv
addLocal x v (bs, lin) = ((x,v):bs, lin)

inEnvironment :: Monad m => r -> ReaderT r m a -> ReaderT r' m a
inEnvironment lenv = withReaderT (const lenv)

stepTerm :: Fresh m => Term -> ExceptT Result (ReaderT LocalEnv m) (Either LocalRes LocalStep)
stepTerm (Jump k v lv) = do
  stk <- evalLValue lv
  v' <- evalValue v
  return (Right $ Jmp k v' stk)
stepTerm (Call f v lv k) = do
  stk <- evalLValue lv
  v' <- evalValue v
  return (Left $ LocalCall f v' (LocalFrame k stk))
stepTerm (LetE e bnd) = do
  (x, m) <- unbind bnd
  v <- evalExpr e
  lenv <- ask
  return (Right $ Step (addLocal x v lenv) m)
stepTerm (If cmp v1 v2 trueb falseb) = do
  v1' <- evalValue v1
  v2' <- evalValue v2
  case (cmp, v1', v2') of
    (Leq, IntV n1, IntV n2) -> do
      let (k, lv) = if n1 <= n2 then trueb else falseb
      stk <- evalLValue lv
      return (Right $ Jmp k UnitV stk)
    _ -> throwError (ErrWrongCompare cmp)
stepTerm (Push v lv bnd) = do
  v' <- evalValue v
  stk <- evalLValue lv
  let stk' = v':stk
  (lv', m) <- unbind bnd
  lenv <- ask
  return (Right $ Step (setStack lv' stk' lenv) m)
stepTerm (Pop lv bnd) = do
  stk <- evalLValue lv
  case stk of
    [] -> throwError (ErrUnexpectedEmptyStack lv)
    (v:stk') -> do
      ((x, lv'), m) <- unbind bnd
      lenv <- ask
      let lenv' = addLocal x v (setStack lv' stk' lenv)
      return (Right $ Step lenv' m)

setStack :: a -> b -> (c, d) -> (c, (a, b))
setStack lv v (vs,_lin) = (vs, (lv, v))

evalExpr :: Monad m => Expr -> ExceptT Result (ReaderT LocalEnv m) Value
evalExpr e =
  case e of
    EValue v -> evalValue v
    EOp op vs -> do
      vs' <- traverse evalValue vs
      case (op, vs') of
        (Add, [IntV n1, IntV n2]) -> return (IntV $! n1 + n2)
        _ -> throwError (ErrWrongOperands op)

evalValue :: Monad m => Value -> ExceptT Result (ReaderT LocalEnv m) Value
evalValue v =
  case v of
    IntV {} -> return v
    UnitV -> return v
    VarV x -> do
      m <- asks (lookup x . fst)
      case m of
        Nothing -> throwError (ErrUnboundVariable x)
        Just v' -> return v'

evalLValue :: Monad m => LinearValue -> ExceptT Result (ReaderT LocalEnv m) [Value]
evalLValue lv = do
  (l, stk) <- asks snd
  case lv of
     VarLV l' ->
       if l == l'
       then return stk
       else throwError (ErrUnboundLV l')
