module Wafl where

import Wafl.Syntax
import Wafl.Stepper

import Control.Monad.Except
import Control.Monad.State.Strict (StateT, runStateT)
import Unbound.Generics.LocallyNameless.Fresh (FreshMT, runFreshMT)

example :: Program
example = program [g1, g2, g3, ev]
  where
    g1 = simple $ FunDecl $ funDefn (fvar "f") (cvar "ret") $
         fnBody (cvar "ret") [ ]
    g2 = simple $ FunDecl $ funDefn (fvar "g") (cvar "ret") $
         fnBody (cvar "enter")
         [
           cont (cvar "enter") (variable "x") (lvar "s") $
           Call (fvar "f") (VarV $ variable "x") (VarLV $ lvar "s") (cvar "ret")
         ]
    g3 = mutualRec [d1, d2]
    d1 = FunDecl $ funDefn (fvar "h") (cvar "ret") $
          fnBody (cvar "enter")
          [
            cont (cvar "enter") (variable "x") (lvar "s") $
            Call (fvar "k") (VarV $ variable "x") (VarLV $ lvar "s") (cvar "ret")
          ]
    d2 = FunDecl $ funDefn (fvar "k") (cvar "ret") $
         fnBody (cvar "enter")
         [
           cont (cvar "enter") (variable "x")  (lvar "s") $
           If Leq (VarV $ variable "x") (IntV 0) (cvar "ret0", VarLV $ lvar "s") (cvar "recu", VarLV $ lvar "s")
         , cont (cvar "ret0") (variable "_") (lvar "s") $
           Jump (cvar "ret") (IntV 0) (VarLV $ lvar "s")
         , cont (cvar "recu") (variable "_") (lvar "s") $
           Call (fvar "h") (VarV $ variable "x") (VarLV $ lvar "s") (cvar "ret")
         ]
    ev = pragmaEval (fvar "g") (IntV 42)

doWafl :: Program -> IO ()
doWafl p = do
  _ <- doIt $ do
    st0 <- initial p
    showState st0
    loop st0
  return ()
  where
    doIt :: Monad m => StateT GlobalEnv (FreshMT m) a -> m (a, GlobalEnv)
    doIt comp = runFreshMT (runStateT comp [])

    showState :: (Show s) => s -> StateT GlobalEnv (FreshMT IO) ()
    showState s = (lift . lift) $ do
      print s
      putStrLn "\n\n"

    showResult :: Result -> StateT GlobalEnv (FreshMT IO) ()
    showResult r = (lift .lift) $ do
      case r of
        Done -> putStrLn "Done"
        _ -> do
          putStrLn "\n!! Error !!\n"
          print r
    loop :: (GlobalCmd, ResidualProgram) -> StateT GlobalEnv (FreshMT IO) ()
    loop (cmd,pgm) = do
      m <- runExceptT (step cmd pgm)
      case m of
        Left r -> showResult r
        Right st -> do
          showState st
          loop st

waflMain :: IO ()
waflMain = return ()
