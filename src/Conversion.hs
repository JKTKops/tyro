module Conversion where

import Control.Arrow
import Data.IntMap qualified as IM
import Data.Map qualified as M
import Data.Set qualified as S
import Data.Functor.Base (TreeF(..))
import Data.Functor.Foldable
import Data.Tree

import Loc
import Constraint
import MLType
import ParserUtils qualified as P
import SMT

data ConstraintInput = CI [(LocIndex, Range)] [ConstraintScheme] [Constraint]
  deriving Show

parseConstraintInput :: P.Parser ConstraintInput
parseConstraintInput = do
  locs <- P.many1 $ (,) <$> locIndex <*> parseRange
  _    <- separator
  scs  <- P.many parseConstraintScheme
  _    <- separator
  cs   <- P.many parseConstraint
  return $ CI locs scs cs
  where
    separator = P.lexeme $ P.string "---"

convert :: ConstraintInput -> [Command]
convert (CI p1 p2 p3)
  = typeDefinition
  : declareLocations
  ++ declareTyVars
  ++ declareSchemes
  ++ assertions
  ++ [Query $ map LocVar $ concatMap flatten ast]
  where
    typeDefinition = DefineType $ allConstructors p2 p3
    declareLocations = locations ast
    declareTyVars = map DeclareTyVar $ S.toList $ S.unions
                  $ map constraintSchemeFvs p2 ++ map constraintFvs p3
    declareSchemes = map (declareScheme ast) p2
    assertions = map Assert $ makeTypingAssertions ast $ locateConstraints p3

    ast = recoverAST p1

allConstructors :: [ConstraintScheme] -> [Constraint] -> [(String, Int)]
allConstructors css cs = M.toList $
  builtins `M.union` constructorsFromSchemes css `M.union` constructorsFromRaws cs
  where
    builtins = M.fromList $ ("->", 2) : map mkTupleN [2..5] -- kinda hacky
    mkTupleN n = ("*" ++ show @Int n, n)

    constructorsFromType (TyCon name args)
      = M.insert name (length args) $ M.unions (map constructorsFromType args)
    constructorsFromType (TyArr t1 t2)
      = constructorsFromType t1 `M.union` constructorsFromType t2
    constructorsFromType (TyTup ts)
      = M.unions $ fmap constructorsFromType ts
    constructorsFromType TyVar{} = M.empty

    constructorsFromRaw (Constrain _ t1 t2)
      = constructorsFromType t1 `M.union` constructorsFromType t2
    constructorsFromRaw (SchemeRef{}) = M.empty
    constructorsFromRaws = M.unions . map constructorsFromRaw

    constructorsFromScheme (Scheme _ _ _ cs0) = constructorsFromRaws cs0
    constructorsFromSchemes = M.unions . map constructorsFromScheme
    

type Weight = Int

locations :: LocAST -> [Command]
locations = map declareOne . concatMap flatten . sizes
  where
    declareOne (li, w) = DeclareLocation (LocVar li) (Just w)

sizes :: LocAST -> Forest (LocIndex, Weight)
sizes = map (fold alg)
  where
    alg :: Base (Tree LocIndex) (Tree (LocIndex, Weight)) -> Tree (LocIndex, Weight)
    alg (NodeF loc subtrees) = Node (loc, w) subtrees
      where
        w = 1 + sum (map (snd . rootLabel) subtrees)

type LocationConstraints = IM.IntMap [Constraint]

locateConstraints :: [Constraint] -> LocationConstraints
locateConstraints = IM.fromListWith (++) . map (constraintLocIx &&& pure)

makeTypingAssertions :: LocAST -> LocationConstraints -> [Assertion]
makeTypingAssertions ast lcs = map (fold alg) ast
  where
    alg :: TreeF Int Assertion -> Assertion
    alg (NodeF locInt subAsserts) =
      Implication (LocVar locInt) $ constraintsHere ++ subAsserts
      where
        constraintsHere = maybe [] (map toAssertion) $ lcs IM.!? locInt
        toAssertion (Constrain _ t1 t2) = SMTConstraint t1 t2
        toAssertion (SchemeRef _ n vs)  = SMTSchemeRef n vs

declareScheme :: LocAST -> ConstraintScheme -> Command
declareScheme ast (Scheme li name vars cs) =
  DeclareScheme name vars $ makeTypingAssertions [subAST] located
  where
    subAST = case findSubAST li ast of
      Just sa -> sa
      Nothing -> error "declareScheme: location was not defined"
    located = locateConstraints cs
