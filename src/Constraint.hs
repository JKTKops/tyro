{-# LANGUAGE ImportQualifiedPost #-}
module Constraint where

import MLType
import Pretty
import ParserUtils qualified as P

data MLConstraint = MLConstrain Type Type Int
  deriving (Eq, Show)

instance Pretty MLConstraint where
  prettyPrec n (MLConstrain s t i)
    = showParen (n > 9) $
      prettyPrec 9 s
    . showString " ="
    . shows i
    . showString "= "
    . prettyPrec 9 t

parseConstraint :: P.Parser MLConstraint
parseConstraint = do
  t1 <- parseType
  n  <- P.lexeme $ P.char '=' *> P.int <* P.char '='
  t2 <- parseType
  return $ MLConstrain t1 t2 n
