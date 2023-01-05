{-# LANGUAGE ImportQualifiedPost #-}
module ParserUtils 
  ( int
  , ident
  , lexeme
  , parens, braces, commaSep
  , module Text.Parsec
  , module Text.Parsec.Char
  , module Text.Parsec.String
  ) where

import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.String
import Text.Parsec.Language (haskellDef)
import Text.Parsec.Token qualified as P

lang :: P.TokenParser ()
lang = P.makeTokenParser $ haskellDef { P.commentLine = "" }

int :: Parser Int
int = fromInteger <$> P.natural lang

ident :: Parser String
ident = P.identifier lang

lexeme :: Parser a -> Parser a
lexeme = P.lexeme lang

parens :: Parser a -> Parser a
parens = P.parens lang

braces :: Parser a -> Parser a
braces = P.braces lang

commaSep :: Parser a -> Parser [a]
commaSep = P.commaSep lang
