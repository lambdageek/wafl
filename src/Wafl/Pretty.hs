{-# language GeneralizedNewtypeDeriving, DataKinds, TypeFamilies, ViewPatterns #-}
module Wafl.Pretty where

import Data.Monoid

import qualified Text.PrettyPrint.ANSI.Leijen as PP

import Unbound.Generics.LocallyNameless.Alpha (Alpha)
import Unbound.Generics.LocallyNameless.Name (Name)
import Unbound.Generics.LocallyNameless.Bind (Bind)
import Unbound.Generics.LocallyNameless.LFresh
import Unbound.Generics.LocallyNameless.Operations (lunbind, unrec, unrebind, unembed)
import Wafl.Syntax

newtype PP a = PP { unPP :: LFreshM a }
             deriving (Functor, Applicative, Monad, LFresh)


data DSort = DMaybePat | DTerm

class Display a where
  type DisplaySort a :: DSort
  disp :: a -> PP PP.Doc

display :: Display a => a -> IO ()
display a = PP.putDoc (runLFreshM $ unPP $ disp a)

cmd :: String -> [PP PP.Doc] -> PP PP.Doc
cmd s m = do
  xs <- sequence m
  return (PP.text s <> PP.space <> PP.parens (PP.align $ PP.fillSep $ PP.punctuate PP.semi xs))

prettyName :: Name a -> PP.Doc
prettyName = PP.text . show

recBlock :: Display a => [a] -> PP PP.Doc
recBlock xs = (\ds -> PP.braces (PP.align $ PP.sep $ combineAnd ds)) <$> traverse disp xs
  where
    combineAnd [] = []
    combineAnd [d] = [d]
    combineAnd (d:ds) = d : map (\d' -> PP.text "and" PP.<+> d') ds

binding :: (Display a, Display b) => a -> b -> PP PP.Doc
binding x y = combine <$> disp x <*> disp y
  where
    combine a b = (a <> PP.dot) PP.</> PP.align b

definedAs :: (Display a, Display b) => a -> b -> PP PP.Doc
definedAs x y = combine <$> disp x <*> disp y
  where
    combine a b = (a PP.<+> PP.text ":=") PP.</> PP.nest 2 (PP.align b)


instance Display CVar where
  type DisplaySort CVar = 'DMaybePat
  disp (CVar k) = disp k

instance Display LVar where
  type DisplaySort LVar = 'DMaybePat
  disp (LVar s) = disp s

instance Display FVar where
  type DisplaySort FVar = 'DMaybePat
  disp (FVar f) = disp f

instance Display (Name a) where
  type DisplaySort (Name a) = 'DMaybePat
  disp = pure . prettyName

instance (Display p1, Display p2, DisplaySort p1 ~ 'DMaybePat, DisplaySort p2 ~ 'DMaybePat, Alpha p1, Alpha p2) => Display (p1, p2) where
  type DisplaySort (p1, p2) = 'DMaybePat
  disp (p1, p2) = combine <$> disp p1 <*> disp p2
    where
      combine a b = PP.align $ PP.fillSep $ PP.punctuate PP.comma [a,b]

instance (Alpha p, Display p, DisplaySort p ~ 'DMaybePat, Alpha t, Display t) => Display (Bind p t) where
  type DisplaySort (Bind p t) = 'DTerm
  disp bnd = lunbind bnd (uncurry binding)

instance Display Program where
  type DisplaySort Program = 'DTerm
  disp (Program bnd) = lunbind bnd (\(ds,()) -> disp ds)

instance Display Decls where
  type DisplaySort Decls = 'DTerm
  disp NilDecls = pure PP.empty
  disp (ConsDecls (unrebind -> (dg, ds))) = combine <$> disp dg <*> disp ds
    where
      combine = (PP.<$>)

instance Display DeclGroup where
  type DisplaySort DeclGroup = 'DTerm
  disp (SingleDecl d) = disp d
  disp (RecDecl ds) = disp ds

instance Display SingleDecl where
  type DisplaySort SingleDecl = 'DTerm
  disp (SimpleDecl d) = disp d
  disp (PragmaDecl p) = disp p

instance Display Pragma where
  type DisplaySort Pragma = 'DTerm
  disp (EvalPragma (unembed -> (f, v))) = cmd ":eval app" [disp f, disp v]
  disp (InfoPragma (unembed -> v)) = (PP.text ":info" PP.<+>) <$> (either disp disp v)

instance Display RecDecls where
  type DisplaySort RecDecls = 'DTerm
  disp (RecDecls (unrec -> ds)) = (\d -> PP.text "rec" PP.</> PP.nest 2 d) <$> recBlock ds

instance Display Decl where
  type DisplaySort Decl = 'DTerm
  disp (FunDecl fdefn) = disp fdefn

instance Display FnDefn where
  type DisplaySort FnDefn = 'DTerm
  disp (FnDefn (unrebind -> (f, unembed -> fn))) = f `definedAs` fn

instance Display Function where
  type DisplaySort Function = 'DTerm
  disp (Function bnd) = cmd "fn" [disp bnd]

instance Display ContDef where
  type DisplaySort ContDef = 'DTerm
  disp (ContDef (unrebind -> (k, unembed -> cdef))) = k `definedAs` cdef

instance Display ContDefs where
  type DisplaySort ContDefs = 'DTerm
  disp (ContDefs (unrec -> ds)) =  (\d -> PP.text "rec" PP.</> PP.nest 2 d) <$> recBlock ds

instance Display FnBody where
  type DisplaySort FnBody = 'DTerm
  disp (FnBody bnd) = lunbind bnd (\(defs,k) -> cmd "let" [disp defs, cmd "enter" [disp k]])

instance Display Continuation where
  type DisplaySort Continuation = 'DTerm
  disp (Continuation bnd) = cmd "cont" [disp bnd]

instance Display Term where
  type DisplaySort Term = 'DTerm
  disp (Jump k v s) = cmd "jump" [disp k, disp v, disp s]
  disp (Call f x s k) = cmd "call" [disp f, disp x, disp s, disp k]
  disp (LetE e bnd) = cmd "let" [disp e, disp bnd]
  disp (Push v lv bnd) = cmd "push" [disp v, disp lv, disp bnd]
  disp (Pop lv bnd) = cmd "pop" [disp lv, disp bnd]
  disp (If Leq v1 v2 (k1,s1) (k2,s2)) = cmd "if<=" [disp v1, disp v2, cmd "then" [disp k1, disp s1],
                                                   cmd "else" [disp k2, disp s2]]

instance Display Expr where
  type DisplaySort Expr = 'DTerm
  disp (EValue v) = disp v
  disp (EOp Add vs) = cmd "add" (map disp vs)

instance Display Value where
  type DisplaySort Value = 'DTerm
  disp (IntV i) = pure $ PP.int i
  disp UnitV    = pure $ PP.text "()"
  disp (VarV x) = disp x

instance Display LinearValue where
  type DisplaySort LinearValue = 'DTerm
  disp (VarLV s) = disp s
