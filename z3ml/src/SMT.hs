module SMT
  ( LocVar(..)
  , Command(..), Assertion(..)
  , SMT(..)
  , outputCommands
  , lookupLoc
  ) where

import Data.IntMap        qualified as IM
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NE
import Constraint
import MLType
import Pretty

newtype LocVar = LocVar Int
  deriving (Eq, Show)

lookupLoc :: LocVar -> IM.IntMap a -> a
lookupLoc (LocVar i) m = m IM.! i

data Command
  -- We've learned that SMT solver runtime tends to EXPLODE if we ever introduce
  -- more than the default -> or *2 constructors with arity >= 2. As a result,
  -- we encode wide tuples as nested *2 pairs, which is not sound.
  = DefineType [(String, Int)] -- names & arities, nothing is implicit
  | DeclareLocation LocVar (Maybe Int) -- optional weight, usually included
  | DeclareTyVar TyVar
  | DeclareScheme SchemeName [TyVar] [Assertion]
  | Assert Assertion
  | Comment String
  | Query [LocVar]
  | GetStats -- get all statistics, processing will have to parse out a time
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

-- | Note that if you swap implementations here, you probably also want to
-- adjust which tuple types are included in Conversion.allConstructors#builtins.
tupToSMT :: NonEmpty Type -> ShowS
tupToSMT = tupToSMTFast

-- | Produce a sound representation of a tuple type, which may cause
-- performance degredation in the SMT solver.
tupToSMTSound :: NonEmpty Type -> ShowS
tupToSMTSound ne = toSMT $ TyCon ("*" ++ show len) (NE.toList ne) where
  len = length ne

-- | Produce a potentially unsound representation of a tuple type, but which
-- is more amenable to typical SMT solvers.
tupToSMTFast :: NonEmpty Type -> ShowS
tupToSMTFast (_ :| [])     = error "tupToSMTFast: solo?"
tupToSMTFast (x :| [y])    = sexp [showString "*2", toSMT x, toSMT y]
tupToSMTFast (x :| (y:ys)) =
  sexp [showString "*2", toSMT x, tupToSMTFast (y :| ys)]

instance SMT Type where
  toSMT = \case
    -- in this case, the name should've been replaced with its nullary index already.
    -- A slightly faster approach would be to just hash the name here, but then we get
    -- really big, weird numbers and it's harder to debug.
    TyCon s []  -> sexp [showString "null", showString s]
    TyCon s tys -> sexp $ showString s : map toSMT tys
    TyArr ty ty' -> toSMT $ TyCon "->" [ty, ty']
    TyTup ne -> tupToSMT ne
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

-- | Encode the given constructors into a Type sort. If you want to adjust
-- whether we use flat (sound) or nested (fast) representation of tuples, you
-- want to adjust tupToSMT above.
defineType :: [(String, Int)] -> ShowS
defineType constructors = sexp
  [ showString "declare-datatype"
  , showString "Type"
    -- (null (nullary Int)) ; for nullary type constructors
    -- ("foo", 3) ==> (foo (foo.1 Type) (foo.2 Type) (foo.3 Type)) ; etc.
  , sexp (nullCtor : map mkConstructor (filter ((> 0) . snd) constructors))]
  where
    nullCtor = sexp [showString "null" , sexp [showString "nullary", showString "Int"]]
    mkConstructor (name, arity) =
      sexp $ showString name : mkFields arity
      where
        mkFields :: Int -> [ShowS]
        mkFields a = map mkField [1 .. a]

        mkField :: Int -> ShowS
        mkField n = sexp [showString name . showChar '.' . shows n, showString "Type"]


instance SMT Command where
  toSMT (DefineType constructors) = defineType constructors
   
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

  toSMT (Comment cmt) = showString $ "; " ++ cmt

  toSMT (Query lvs)
    = sexp [showString "check-sat"]
    . sexp [showString "get-objectives"]
    . sexp [showString "get-value", sexp (map toSMT lvs)]

  toSMT GetStats = sexp $ map showString ["get-info", ":all-statistics"]

