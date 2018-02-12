-- | Convert text input into Wafl presyntax.
{-# language OverloadedStrings, ConstraintKinds #-}
module Wafl.Parser where

import Control.Applicative hiding (many)
import Data.Char
import Data.Void

import qualified Data.Text.Lazy as T

import Text.Megaparsec
import qualified Text.Megaparsec.Char as L hiding (space)
import qualified Text.Megaparsec.Char.Lexer as L
  
import Wafl.PreSyntax

type ParserT = ParsecT Void T.Text
type MonadParser = MonadParsec Void T.Text

var :: MonadParser m => m Var
var = Var <$> identifier

bind :: MonadParser m => m p -> m t -> m (Bind p t)
bind = liftA2 Bind
  
value :: MonadParser m => m Value
value = label "value" valueParser
  where
    valueParser = IntV <$> int
      <|> UnitV <$ keyword "unit"
      <|> VarV <$> var

linearValue :: MonadParser m => m LinearValue
linearValue = label "linear value" (VarLV <$> var)

expr :: MonadParser m => m Expr
expr = label "expression" exprParser
  where
    exprParser = addend
    addend = mkAddend <$> factor <*> optional (plus *> factor)
    factor = value
    plus = reservedOp "+"
    mkAddend l (Just r) = EOp Add [l, r]
    mkAddend l Nothing = EValue l

term :: MonadParser m => m Term
term = label "term" termParser
  where
    termParser = jumpTerm <|> callTerm <|> letTerm
      <|> pushTerm <|> popTerm
      <|> ifTerm
    jumpTerm = Jump <$ keyword "jmp" <*> var <*> value <*> linearValue
    callTerm = Call <$ keyword "call" <*> var <*> value <*> linearValue <*> var
    letTerm = LetE <$ keyword "let" <*> expr <* keyword "be" <*> bind (var <* keyword "in") term
    pushTerm = empty
    popTerm = empty
    ifTerm = empty

---- Lexer

lexeme :: MonadParser m => m a -> m a
lexeme = L.lexeme spaceConsumer

spaceConsumer :: MonadParser m => m ()
spaceConsumer = L.space L.space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

parens :: MonadParser m => m a -> m a
parens = between (symbol "(") (symbol ")")

symbol :: MonadParser m => T.Text -> m T.Text
symbol = L.symbol spaceConsumer

int :: MonadParser m => m Int
int = lexeme L.decimal

keyword :: MonadParser m => T.Text -> m ()
keyword w = lexeme (L.string w *> notFollowedBy L.alphaNumChar)

reservedOp :: MonadParser m => T.Text -> m ()
reservedOp w = lexeme (L.string w *> notFollowedBy L.symbolChar)

rws :: [T.Text] -- list of reserved words
rws = ["jmp", "call", "let", "be", "in", "push", "to", "if", "then", "else"
      , "unit"
      ]

rops :: [T.Text] -- reserved operators
rops = ["▷", "+", "<"]

identifier :: MonadParser m => m T.Text 
identifier = (lexeme . try) (p >>= check)
  where
    p       = T.cons <$> L.letterChar <*> takeWhileP (Just "alphanumeric") isAlphaNum
    check x = if x `elem` rws
                then fail $ "keyword " ++ show x ++ " cannot be an identifier"
                else return x
