module SMT
  ( LocVar(..)
  , Command(..), Assertion(..)
  , SMT(..)
  , outputCommands
  ) where

import Data.List.NonEmpty qualified as NE
import Constraint
import MLType
import Pretty

newtype LocVar = LocVar Int
  deriving (Eq, Show)

data Command
  = DefineType [(String, Int)] -- names & arities, nothing is implicit
  | DeclareLocation LocVar (Maybe Int) -- optional weight, usually included
  | DeclareTyVar TyVar
  | DeclareScheme SchemeName [TyVar] [Assertion]
  | Assert Assertion
  | Query [LocVar]
  deriving (Eq, Show)

outputCommands :: [Command] -> String -- Text?
outputCommands = unlines . map (($"") . toSMT)

data Assertion
  = SMTConstraint Type Type
  | SMTSchemeRef SchemeName [TyVar]
  | Implication LocVar [Assertion]
  deriving (Eq, Show)

parens :: ShowS -> ShowS
parens = showParen True

sexp :: [ShowS] -> ShowS
sexp [] = parens id
sexp (s:ss) = parens $ s . foldr (\s' dl -> showChar ' ' . s' . dl) id ss

class SMT a where
  toSMT :: a -> ShowS
  -- toPrettySMT :: a -> Doc  

instance SMT LocVar where
  toSMT (LocVar l) = showChar 'T' . shows l

instance SMT TyVar where
  toSMT = prettyPrec 0

instance SMT Type where
  toSMT = \case
    TyCon s []  -> showString s
    TyCon s tys -> sexp $ showString s : map toSMT tys
    TyArr ty ty' -> toSMT $ TyCon "->" [ty, ty']
    TyTup ne -> toSMT $ TyCon ("*" ++ show len) (NE.toList ne)
      where len = length ne
    TyVar tv -> toSMT tv

instance SMT Assertion where
  toSMT (SMTConstraint t1 t2) = sexp [showString "=", toSMT t1, toSMT t2]
  toSMT (SMTSchemeRef name vars) = sexp $ showString name : map toSMT vars
  toSMT (Implication _ []) = showString "true"
  toSMT (Implication loc as) = loc `implies` mkAnd as
    where
      implies l s = sexp [showString "=>", toSMT l, s]

mkAnd :: [Assertion] -> ShowS
mkAnd [] = showString "true"
mkAnd [a] = toSMT a
mkAnd as' = sexp (showString "and" : map toSMT as')

instance SMT Command where
  toSMT (DefineType constructors) = sexp
    [ showString "declare-datatype"
    , showString "Type"
    , sexp (map mkConstructor constructors)]
    where
      mkConstructor (name, arity) =
        sexp $ showString name : mkFields arity
        where
          mkFields :: Int -> [ShowS]
          mkFields a = map mkField [1 .. a]

          mkField :: Int -> ShowS
          mkField n = sexp [showString name . showChar '.' . shows n, showString "Type"]
  
  toSMT (DeclareLocation loc mw) =
    sexp [showString "declare-const", toSMT loc, showString "Bool"]
    . sexp (assert mw : toSMT loc : weight mw)
    where
      assert Nothing  = showString "assert"
      assert Just{}   = showString "assert-soft"
      weight Nothing  = []
      weight (Just w) = [showString ":weight", shows w]

  toSMT (DeclareTyVar tv) =
    sexp [showString "declare-const", toSMT tv, showString "Type"]

  toSMT (DeclareScheme name vars assertions) =
    sexp [showString "define-fun", showString name
         , mkFormals vars, showString "Bool"
         , mkAnd assertions]
    where
      mkFormals = sexp . map mkFormal
      mkFormal v = sexp [toSMT v, showString "Type"]

  toSMT (Assert assertion) = sexp [showString "assert", toSMT assertion]

  toSMT (Query lvs)
    = sexp [showString "check-sat"]
    . sexp [showString "get-objectives"]
    . sexp [showString "get-value", sexp (map toSMT lvs)]

