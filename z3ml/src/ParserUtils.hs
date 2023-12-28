{-# LANGUAGE ImportQualifiedPost #-}
module ParserUtils 
  ( int, double
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
import Text.Parsec.Language (emptyDef, haskellDef)
import Text.Parsec.Token qualified as P

lang :: P.TokenParser ()
lang = P.makeTokenParser $ emptyDef
  { P.identStart  = P.identStart haskellDef
  , P.identLetter = char '.' <|> P.identLetter haskellDef
  }

int :: Parser Int
int = fromInteger <$> P.natural lang

double :: Parser Double
double = try (P.float lang) <|> (fromIntegral <$> int)

-- We must allow identifiers like foo' when parsing input, but
-- smtlib does NOT allow apostrophes in identifer names. To fix this,
-- we use an encoding scheme to hide the ' with symbols that are allowed:
-- replace ' with ^- and replace ^ with ^^. ^ is very rare (only appears
-- in custom operators) so we're pretty much free to use it.
ident :: Parser String
ident = fixup <$> P.identifier lang where
  fixup = concatMap encodeApo
  encodeApo '\'' = "^-"
  encodeApo '^'  = "^^"
  encodeApo c    = [c]

lexeme :: Parser a -> Parser a
lexeme = P.lexeme lang

parens :: Parser a -> Parser a
parens = P.parens lang

braces :: Parser a -> Parser a
braces = P.braces lang

commaSep :: Parser a -> Parser [a]
commaSep = P.commaSep lang
