module Constraint
  ( SchemeName
  , Constraint(..), ConstraintScheme(..)
  , constraintLocIx, constraintFvs, constraintSchemeFvs
  , parseConstraint, parseConstraintScheme
  ) where

import Data.Set qualified as S

import Loc
import MLType
import Pretty
import ParserUtils qualified as P

type SchemeName = String

data Constraint
  = Constrain LocIndex Type Type
  | SchemeRef LocIndex SchemeName [TyVar]
  deriving (Eq, Show)

constraintLocIx :: Constraint -> Int
constraintLocIx (Constrain li _ _) = li
constraintLocIx (SchemeRef li _ _) = li

constraintFvs :: Constraint -> FreeVars
constraintFvs (Constrain _ t1 t2) = typeFvs t1 `S.union` typeFvs t2
constraintFvs (SchemeRef _ _ tvs) = S.fromList tvs

data ConstraintScheme = Scheme LocIndex SchemeName [TyVar] [Constraint]
  deriving Show

constraintSchemeFvs :: ConstraintScheme -> FreeVars
constraintSchemeFvs (Scheme _ _ qvs cs) =
  S.unions (map constraintFvs cs) `S.difference` S.fromList qvs

intercalateS :: ShowS -> [ShowS] -> ShowS
intercalateS _   []     = id
intercalateS _   [x]    = x
intercalateS sep (x:xs) = x . sep . intercalateS sep xs

prettyVars :: [TyVar] -> ShowS
prettyVars = intercalateS (showString ", ") . map (prettyPrec 0)

instance Pretty Constraint where
  prettyPrec _ (Constrain i s t)
    = shows i
    . showString " "
    . prettyPrec 9 s
    . showString " = "
    . prettyPrec 9 t
  prettyPrec _ (SchemeRef i name vars)
    = shows i . showChar ' '
    . showString name . showParen True (prettyVars vars)
instance Pretty ConstraintScheme where
  prettyPrec _ (Scheme li n vars cs)
    = shows li . showChar ' ' . showString n
    . showString " ∀(" . prettyVars vars . showString ") { "
    . intercalateS (showString "\n  ") (map (prettyPrec 10) cs)
    . showString " }"

parseConstraint :: P.Parser Constraint
parseConstraint = do
  n  <- locIndex
  t1 <- parseType
  thenConstraint n t1 P.<|> thenScheme n t1
  where
    thenConstraint n t1 = do
      _  <- P.lexeme $ P.char '='
      t2 <- parseType
      return $ Constrain n t1 t2
    thenScheme n t1 = P.parens $ case t1 of
      TyCon name [] -> SchemeRef n name <$> P.commaSep parseTyVar
      _ -> P.parserFail "Can't parse constraint"

parseConstraintScheme :: P.Parser ConstraintScheme
parseConstraintScheme =
  Scheme <$> locIndex
         <*> parseName
         <*> P.parens (P.commaSep parseTyVar)
         <*> P.braces (P.many parseConstraint)
