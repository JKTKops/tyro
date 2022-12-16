{-# LANGUAGE ImportQualifiedPost #-}
module ParserUtils 
  ( int
  , ident
  , lexeme
  , parens
  , module Text.Parsec
  , module Text.Parsec.Char
  , module Text.Parsec.String
  ) where

import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.String
import Text.Parsec.Language (haskell)
import Text.Parsec.Token qualified as P

int :: Parser Int
int = fromInteger <$> P.natural haskell

ident :: Parser String
ident = P.identifier haskell

lexeme :: Parser a -> Parser a
lexeme = P.lexeme haskell

parens :: Parser a -> Parser a
parens = P.parens haskell
