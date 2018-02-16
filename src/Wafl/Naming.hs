-- | Convert from PreSyntax to Syntax
{-# language GADTs, DataKinds, TypeFamilies, GeneralizedNewtypeDeriving, LambdaCase #-}
module Wafl.Naming where


import Control.Monad.Reader (ReaderT(..))
import Control.Monad.Reader.Class (MonadReader(..), asks)
import Control.Monad.Except (ExceptT(..))
import Control.Monad.Error.Class (MonadError (..))

import qualified Data.Map as M
import Data.Type.Equality

import Unbound.Generics.LocallyNameless

import qualified Wafl.PreSyntax as P
import qualified Wafl.Syntax as S

-- | The sorts of variables we have in the syntax.
-- This is used both at the value level
-- and promoted as a kind.
data VarSort = FunVS | ContVS | LinVS | VarVS
  deriving Show

-- | Singleton type for 'VarSort'
data VarSortS (s :: VarSort) where
  FunVSS :: VarSortS 'FunVS
  ContVSS :: VarSortS 'ContVS
  LinVSS :: VarSortS 'LinVS
  VarVSS :: VarSortS 'VarVS

-- | Demote the 'VarSort' given by the singleton to a value.
demoteVarSort :: VarSortS s -> VarSort
demoteVarSort FunVSS = FunVS
demoteVarSort ContVSS = ContVS
demoteVarSort LinVSS = LinVS
demoteVarSort VarVSS = VarVS

instance TestEquality VarSortS where
  testEquality FunVSS FunVSS = Just Refl
  testEquality ContVSS ContVSS = Just Refl
  testEquality LinVSS LinVSS = Just Refl
  testEquality VarVSS VarVSS = Just Refl
  testEquality _ _ = Nothing


-- | The type of "Wafl.Syntax" variables corresponding to the given 'VarSort'
type family VarSyntax (s :: VarSort) :: * where
  VarSyntax 'FunVS = S.FVar
  VarSyntax 'ContVS = S.CVar
  VarSyntax 'LinVS = S.LVar
  VarSyntax 'VarVS = S.Variable

-- | Make a fresh syntax variable of the apropriate sort from
-- the given presyntax variable.
freshVar :: Fresh m => P.Var -> VarSortS s -> m (VarSyntax s)
freshVar p =
  let s = P.varNameS p
  in \case
    FunVSS -> S.FVar <$> fresh (s2n s)
    ContVSS -> S.CVar <$> fresh (s2n s)
    LinVSS -> S.LVar <$> fresh (s2n s)
    VarVSS -> fresh (s2n s)
                     

-- | Existentially qualify over a variable sort and the corresponding
-- syntactic variable.
data AnyVar where
  AnyVar :: VarSortS s -> VarSyntax s -> AnyVar

-- | Environment used during the naming pass that maps
-- pres-syntax variables to their syntactic sort and the corresponding
-- syntactic variable.
newtype Env = Env { envVars :: M.Map P.Var AnyVar }

-- | Naming may fail if a pre-syntax variable was unbound, or it's used
-- where a variable of a different sort was expected.
data NamingErr = WrongVarErr P.Var VarSort VarSort
  | UnboundVarErr P.Var
  deriving (Show)

-- | Monad in which we may do naming.
class Applicative m => MonadNaming m where
  -- | Extend the naming environment by adding the given presyntax
  -- variable of the given sort, mapping it to a fresh syntax variable
  -- of the given sort and running the given computation with the new
  -- variable in scope.
  withVar :: P.Var -> VarSortS s -> (VarSyntax s -> m r) -> m r
  -- | Look up the given presyntax variable expecting the result to be
  -- of the given sort.
  lookupVar :: VarSortS s -> P.Var -> m (VarSyntax s)

var :: MonadNaming m => P.Var -> m S.Variable
var = lookupVar VarVSS

cvar :: MonadNaming m => P.Var -> m S.CVar
cvar = lookupVar ContVSS

lvar :: MonadNaming m => P.Var -> m S.LVar
lvar = lookupVar LinVSS

fvar :: MonadNaming m => P.Var -> m S.FVar
fvar = lookupVar FunVSS

-- | The class of pre-syntax values that may be translated by the naming pass
class Nameable p where
  -- | The syntax you get by running naming  on the given pre-syntax
  type Named p :: *
  -- | Perform naming on the given presyntax
  name :: MonadNaming m => p -> m (Named p)

instance Nameable P.Op where
  type Named P.Op = S.Op
  name P.Add = pure S.Add

instance Nameable P.Cmp where
  type Named P.Cmp = S.Cmp
  name P.Leq = pure S.Leq

instance Nameable P.Value where
  type Named P.Value = S.Value
  name (P.IntV j) = pure (S.IntV j)
  name P.UnitV = pure S.UnitV
  name (P.VarV v) = S.VarV <$> var v

instance Nameable P.LinearValue where
  type Named P.LinearValue = S.LinearValue
  name (P.VarLV v) = S.VarLV <$> lvar v

instance Nameable P.Expr where
  type Named P.Expr = S.Expr
  name (P.EValue v) = S.EValue <$> name v
  name (P.EOp o vs) = S.EOp <$> name o <*> traverse name vs
  
instance Nameable P.Term where
  type Named P.Term = S.Term
  name (P.Jump k v lv) = S.Jump <$> cvar k <*> name v <*> name lv
  name (P.Call f v lv k) = S.Call <$> fvar f <*> name v <*> name lv <*> cvar k
  name (P.LetE e (P.Bind x m)) = S.LetE <$> name e <*> withVar x VarVSS (\x' -> bind x' <$> name m) 
  name (P.Push v lv (P.Bind l m)) = S.Push <$> name v <*> name lv <*> withVar l LinVSS (\l' -> bind l' <$> name m)
  name (P.Pop lv (P.Bind (x, l) m)) = S.Pop <$> name lv <*> withVar x VarVSS (\x' -> withVar l LinVSS (\l' -> bind (x', l') <$> name m))
  name (P.If cmp v1 v2 br1 br2) =
    let br (k, lv) = (,) <$> cvar k <*> name lv
    in S.If <$> name cmp <*> name v1 <*> name v2 <*> br br1 <*> br br2

-- | A concrete monad transformer for naming
newtype NamingT m a = NamingT { unNamingT :: ReaderT Env (ExceptT NamingErr (FreshMT m)) a }
  deriving (Functor, Applicative, Monad)

instance Monad m => MonadNaming (NamingT m) where
  withVar p vs k = NamingT $ do
    x <- freshVar p vs
    local (Env . M.insert p (AnyVar vs x) . envVars) (unNamingT $ k x)
  lookupVar vs p = NamingT $ do
    m <- asks (M.lookup p . envVars)
    case m of
      Nothing -> throwError (UnboundVarErr p)
      Just (AnyVar vs' x) -> case testEquality vs vs' of
        Just Refl -> return x
        Nothing -> throwError (WrongVarErr p (demoteVarSort vs) (demoteVarSort vs'))
