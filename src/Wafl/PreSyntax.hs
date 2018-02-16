-- | Defines the pre-syntax for Wafl
--
-- The presyntax does not distinguish identifier categories (variable,
-- linear variable, function name, etc) and it does not represent binding.
module Wafl.PreSyntax where

import qualified Data.Text.Lazy as T

data Bind p t = Bind p t
  deriving (Show)

newtype Var = Var  { varName :: T.Text }
  deriving (Eq, Ord, Show)

varNameS :: Var -> String
varNameS = T.unpack . varName

data Term =
  Jump Var Value LinearValue
  | Call Var Value LinearValue Var
  | LetE Expr (Bind Var Term)
  | Push Value LinearValue (Bind Var Term)
  | Pop LinearValue (Bind (Var, Var) Term)
  | If Cmp Value Value (Var, LinearValue) (Var, LinearValue)
    deriving (Show)

data Expr = EValue Value
          | EOp Op [Value]
          deriving (Show)

data LinearValue = VarLV Var
  deriving (Show)

data Value = IntV !Int
  | UnitV
  | VarV Var
  deriving (Show)

data Op = Add
  deriving (Show)

data Cmp = Leq
  deriving (Show)

