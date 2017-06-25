{-# language DeriveGeneric #-}
module Wafl.Syntax where

import GHC.Generics
import Unbound.Generics.LocallyNameless

newtype Program = Program (Bind Decls ())
                deriving (Show, Generic)

-- patterns

data Decls = NilDecls
           | ConsDecls (Rebind DeclGroup Decls)
           deriving (Show, Generic)

data DeclGroup = SingleDecl SingleDecl
          | RecDecl RecDecls
          deriving (Show, Generic)

data SingleDecl =
  -- decl
  SimpleDecl Decl
  -- :pragma
  | PragmaDecl Pragma
  deriving (Show, Generic)

newtype RecDecls = RecDecls { recDecls :: Rec [Decl] }
                 deriving (Show, Generic)

data Decl =
  -- fun f = ...
  FunDecl FnDefn
  deriving (Show, Generic)

-- fun f = λ (kret:B→0) . letrec { …, kenter = cont (x:A) (s^1) . m, … } in kenter
newtype FnDefn = FnDefn (Rebind FVar (Embed Function))
                 deriving (Show, Generic)

data Pragma =
  -- :eval f v
  EvalPragma (Embed (FVar, Value))
  -- :info f | :info x
  | InfoPragma (Embed (Either FVar Variable))
               deriving (Show, Generic)

newtype FVar = FVar { fvarName :: Name FVar }
             deriving (Eq, Show, Generic)

newtype CVar = CVar {cvarName :: Name CVar }
             deriving (Eq, Show, Generic)

type Variable = Name Value

newtype LVar = LVar { lvarName :: Name LVar }
                  deriving (Eq, Show, Generic)

newtype ContDefs = ContDefs { contDefs :: Rec [ContDef]}
                 deriving (Show, Generic)

-- cont k = cont (x:A) . m
newtype ContDef = ContDef (Rebind CVar (Embed Continuation))
                deriving (Show, Generic)

-- terms

-- λ(kret:B→0) . body
newtype Function = Function (Bind CVar FnBody)
               deriving (Show, Generic)

-- letrec { contDefs } in enter k
newtype FnBody = FnBody (Bind ContDefs CVar)
               deriving (Show, Generic)

-- cont (x : A) (s^L). m
newtype Continuation = Continuation (Bind (Variable, LVar) Term)
                     deriving (Show, Generic)

data Term =
  -- jmp k v s
  Jump CVar Value LinearValue
  -- call f v s k 
  | Call FVar Value LinearValue CVar
  -- let e be x in m
  | LetE Expr (Bind Variable Term)
  -- push v▷s to s' in m
  |  Push Value LinearValue (Bind LVar Term)
  -- pop s to (x▷s') in m
  | Pop LinearValue (Bind (Variable, LVar) Term)
  -- if cmp v1 v2 then k () s else k' () s
  | If Cmp Value Value (CVar, LinearValue) (CVar, LinearValue)
  deriving (Show, Generic)

data Expr = EValue Value
          | EOp Op [Value]
          deriving (Show, Generic)

newtype LinearValue = VarLV LVar
  deriving (Show, Generic)

data Value = IntV !Int
           | UnitV
           | VarV Variable
           deriving (Show, Generic)

data Op = Add
        deriving (Show, Generic)

data Cmp = Leq
         deriving (Show, Generic)


instance Alpha Program
instance Alpha Decls
instance Alpha DeclGroup
instance Alpha SingleDecl
instance Alpha RecDecls
instance Alpha Decl
instance Alpha FnDefn
instance Alpha Pragma

instance Alpha FVar
instance Alpha CVar
instance Alpha LVar

instance Alpha ContDefs
instance Alpha ContDef

instance Alpha Function
instance Alpha FnBody
instance Alpha Continuation
instance Alpha Term
instance Alpha Expr
instance Alpha LinearValue
instance Alpha Value

instance Alpha Op
instance Alpha Cmp


-- Conveniences
fvar :: String -> FVar
fvar = FVar . s2n

cvar :: String -> CVar
cvar = CVar . s2n

variable :: String -> Variable
variable = s2n

lvar :: String -> LVar
lvar = LVar . s2n

program :: [DeclGroup] -> Program
program = Program . flip bind () . mkDecls
  where
    mkDecls :: [DeclGroup] -> Decls
    mkDecls = foldr (\dg ds -> ConsDecls $ rebind dg ds) NilDecls

simple :: Decl -> DeclGroup
simple = SingleDecl . SimpleDecl 

mutualRec :: [Decl] -> DeclGroup
mutualRec = RecDecl . RecDecls . rec

pragmaEval :: FVar -> Value -> DeclGroup
pragmaEval f v = SingleDecl $ PragmaDecl $ EvalPragma $ embed (f, v)

-- fun f (kret:B→0) = body
funDefn :: FVar -> CVar -> FnBody -> FnDefn
funDefn f k = FnDefn . rebind f . embed . Function . bind k 

fnBody :: CVar -> [ContDef] -> FnBody
fnBody kenter = FnBody . flip bind kenter . ContDefs . rec

-- cont k (x:A) (s^L) = m
cont :: CVar -> Variable -> LVar -> Term -> ContDef
cont k x s = ContDef . rebind k . embed . Continuation . bind (x, s)

letE :: Expr -> Variable -> Term -> Term
letE e x = LetE e . bind x

push :: Value -> LinearValue -> LVar -> Term -> Term
push v lv lv' = Push v lv . bind lv'

pop :: LinearValue -> Variable -> LVar -> Term -> Term
pop lv x lv' = Pop lv . bind (x, lv')
