{-# LANGUAGE LambdaCase, ImportQualifiedPost #-}
module SMT where

import Data.IntMap qualified as M
import Data.List.NonEmpty qualified as NE
import Loc (LocAST)
import Constraint
import MLType
import Data.Functor.Base (TreeF(..))
import Data.Functor.Foldable
import Data.Maybe (fromMaybe)

newtype LocVar = LocVar Int
  deriving (Eq, Show)

data Command
  = DefineType [(String, Int)] -- names & arities, nothing is implicit
  | DeclareLocation LocVar (Maybe Int) -- optional weight, usually included
  | DeclareTyVar TyVar
  | Assert Assertion
  deriving (Eq, Show)

data Assertion
  = SMTConstraint Type Type
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
  toSMT (TV name mi) = showString name . showi
    where
      showi = case mi of
        Nothing -> id
        Just i  -> showChar '.' . shows i

instance SMT Type where
  toSMT = \case
    TyCon s tys -> sexp $ showString s : map toSMT tys
    TyArr ty ty' -> toSMT $ TyCon "->" [ty, ty']
    TyTup ne -> toSMT $ TyCon ("*" ++ show len) (NE.toList ne)
      where len = length ne
    TyVar tv -> toSMT tv

instance SMT Assertion where
  toSMT (SMTConstraint t1 t2) = sexp [showString "=", toSMT t1, toSMT t2]
  toSMT (Implication _ []) = showString "true"
  toSMT (Implication loc as) = loc `implies` mkAnd as
    where
      implies l s = sexp [showString "=>", toSMT l, s]
      mkAnd [] = showString "true"
      mkAnd [a] = toSMT a
      mkAnd as' = sexp (showString "and" : map toSMT as')

instance SMT Command where
  toSMT (DefineType constructors) = sexp $
    showString "define-type" :
    showString "Type" :
    sexp [] :
    map mkConstructor constructors
    where
      mkConstructor (name, arity) =
        sexp $ showString name : mkFields arity
        where
          mkFields :: Int -> [ShowS]
          mkFields a = map mkField [1 .. a]

          mkField :: Int -> ShowS
          mkField n = showString name . showChar '.' . shows n
  
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

  toSMT (Assert assertion) = sexp [showString "assert", toSMT assertion]

type HardLocations = M.IntMap LocVar
type LocationConstraints = M.IntMap [MLConstraint]

makeTypingAssertions :: LocAST -> LocationConstraints -> [Assertion]
makeTypingAssertions ast lcs = map (fold alg) ast
  where
    alg :: TreeF Int Assertion -> Assertion
    alg (NodeF locInt subAsserts) =
      Implication (LocVar locInt) $ constraintsHere ++ subAsserts
      where
        constraintsHere = maybe [] (map toAssertion) $ lcs M.!? locInt
        toAssertion (MLConstrain t1 t2 _) = SMTConstraint t1 t2
