module Conversion where

import Control.Arrow
import Data.IntMap qualified as IM
import Data.Map qualified as M
import Data.Set qualified as S
import Data.Maybe (fromMaybe, fromJust)
import Data.Functor.Base (TreeF(..))
import Data.Functor.Foldable
import Data.Tree

import Loc
import Constraint
import MLType
import ParserUtils qualified as P
import SMT

type Weight = Int

data ConstraintInput = CI [(LocIndex, Range, Maybe Weight)] [ConstraintScheme] [Constraint]
  deriving Show

parseConstraintInput :: P.Parser ConstraintInput
parseConstraintInput = do
  locs <- P.many1 $ (,,) <$> locIndex <*> parseRange <*> (weight <* semi)
  _    <- separator
  scs  <- P.many parseConstraintScheme
  _    <- separator
  cs   <- P.many parseConstraint
  return $ CI locs scs cs
  where
    separator = P.lexeme $ P.string "---"
    weight = P.lexeme $ P.optionMaybe P.int
    semi = P.lexeme $ P.char ';'

parseInput :: FilePath -> String -> Either P.ParseError ConstraintInput
parseInput = P.parse parseConstraintInput

convert :: ConstraintInput -> [Command]
convert (CI p1 p2 p3)
  = typeDefinition
  : nullaryCtorComment
  ++ declareLocations
  ++ declareTyVars
  ++ declareSchemes
  ++ assertions
  ++ [Query $ map (LocVar . fst) $ concatMap flatten ast
     ,GetStats]
  where
    ctors = allConstructors p2 p3
    nullaryCtors = map fst (filter ((== 0) . snd) ctors) `zip` [0..]
    nullaryCtorComment = map mkCtorComment nullaryCtors

    typeDefinition = DefineType ctors
    p2' = map (zapNullariesS nullaryCtors) p2
    p3' = map (zapNullariesC nullaryCtors) p3
    declareLocations = locations ast
    declareTyVars = map DeclareTyVar $ S.toList $ S.unions
                  $ map constraintSchemeFvs p2' ++ map constraintFvs p3'
    -- TODO: These need to be emitted from the leaves of the tree towards the root.
    declareSchemes = map (declareScheme ast) $ sortSchemes ast p2'
    assertions = map Assert $ makeTypingAssertions ast $ locateConstraints p3'

    ast = recoverAST p1

zapNullariesS :: [(String, Int)] -> ConstraintScheme -> ConstraintScheme
zapNullariesS ctors (Scheme li n tvs cs) =
  Scheme li n tvs (map (zapNullariesC ctors) cs)

zapNullariesC :: [(String, Int)] -> Constraint -> Constraint
zapNullariesC ctors (Constrain li t1 t2) =
  Constrain li (zapNullariesT ctors t1) (zapNullariesT ctors t2)
zapNullariesC _ctors (SchemeRef li n tvs) = SchemeRef li n tvs

zapNullariesT :: [(String, Int)] -> Type -> Type
zapNullariesT ctors = go where
  go (TyCon name []) = TyCon (show $ fromJust $ lookup name ctors) []
  go (TyCon name ts) = TyCon name (fmap go ts)
  go (TyArr t1 t2)   = TyArr (go t1) (go t2)
  go (TyTup ts)      = TyTup (fmap go ts)
  go (TyVar n)       = TyVar n

mkCtorComment :: (String, Int) -> Command
mkCtorComment (name, ix) = Comment $ name ++ " ==> " ++ show ix

getRangeMapping :: ConstraintInput -> IM.IntMap Range
getRangeMapping (CI p _ _) = IM.fromList [ (loc,r) | (loc,r,_) <- p ]

allConstructors :: [ConstraintScheme] -> [Constraint] -> [(String, Int)]
allConstructors css cs = M.toList $
  builtins `M.union` constructorsFromSchemes css `M.union` constructorsFromRaws cs
  where
    -- in FAST mode, don't generate *3,*4, or *5.
    builtins = M.fromList [("->", 2) ,  mkTupleN 2]
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
    

locations :: LocAST -> [Command]
locations = map declareOne . concatMap flatten . weights
  where
    declareOne (li, 0) = DeclareLocation (LocVar li) Nothing
    declareOne (li, w) = DeclareLocation (LocVar li) (Just w)

weights :: LocAST -> Forest (LocIndex, Weight)
weights = map (fold alg)
  where
    alg :: Base (Tree (LocIndex, Maybe Weight)) (Tree (LocIndex, Weight))
        -> Tree (LocIndex, Weight)
    alg (NodeF (loc, Just w) subtrees) = Node (loc, w) subtrees
    alg (NodeF (loc, Nothing) subtrees) = Node (loc, w) subtrees
      where
        w = 1 + sum (map (snd . rootLabel) subtrees)

type LocationConstraints = IM.IntMap [Constraint]

locateConstraints :: [Constraint] -> LocationConstraints
locateConstraints = IM.fromListWith (++) . map (constraintLocIx &&& pure)

-- One-stop-shop to replace the current typing assertion generator.
makeTypingAssertions :: LocAST -> LocationConstraints -> [Assertion]
makeTypingAssertions = makeTypingAssertionsAsWies

-- make typing assertions in the style we want to investigate; i.e.
-- for every node N in the AST, emit ((and (path..to..N)) => constraints-at-N)
makeTypingAssertionsAsFlat :: LocAST -> LocationConstraints -> [Assertion]
makeTypingAssertionsAsFlat = undefined

-- make typing assertions in the style of the Wies artifact; i.e.
-- for every edge in the AST, emit (P => (C => constraints-at-C))
-- but also emit (R => constraints-at-R) for each root so we don't lose those.
makeTypingAssertionsAsWies :: LocAST -> LocationConstraints -> [Assertion]
makeTypingAssertionsAsWies ast lcs = concatMap (hdl . fold alg) (dropWeights ast)
  where
    hdl (complete, root) = root : complete
    csHere = constraintsHere lcs
    -- An AST algebra over pairs of "all complete assertions" and "single-location assertions."
    -- Each location produces the single-loc assert (Here => constraints-Here) but also
    -- combines the single-loc asserts of its children into complete assertions of the form
    -- (Here => (child-single-loc-assert)).
    alg :: TreeF LocIndex ([Assertion], Assertion) -> ([Assertion], Assertion)
    alg (NodeF locInt children) = (allComplete, Implication (LocVar locInt) here) where
      here = csHere locInt
      allComplete = hereComplete ++ childrenComplete
      hereComplete = map (Implication (LocVar locInt) . pure . snd) children
      childrenComplete = concatMap fst children

-- make typing assertions in the style of the Wies paper; i.e.
-- for ever root, emit (R => (and constraints-at-R (C1 => ...) (C2 => ...)))
-- repeating recursively down the whole tree rooted at R.
makeTypingAssertionsAsPaper :: LocAST -> LocationConstraints -> [Assertion]
makeTypingAssertionsAsPaper ast lcs = map (fold alg) $ dropWeights ast
  where
    csHere = constraintsHere lcs
    alg :: TreeF LocIndex Assertion -> Assertion
    alg (NodeF locInt subAsserts) =
      Implication (LocVar locInt) $ csHere locInt ++ subAsserts
        
constraintsHere :: LocationConstraints -> LocIndex -> [Assertion]
constraintsHere lcs locInt = maybe [] (map toAssertion) $ lcs IM.!? locInt

toAssertion :: Constraint -> Assertion
toAssertion (Constrain _ t1 t2) = SMTConstraint t1 t2
toAssertion (SchemeRef _ n vs)  = SMTSchemeRef n vs

dropWeights :: LocAST -> Forest LocIndex
dropWeights = fmap (fmap fst)

-- | z3 will cry if we try to refer to a scheme before it is defined.
--   But any local binding is going to result in a scheme, and the binding
--   to which it is local is going to refer to it. Therefore, it is
--   critical that we emit schemes in an order consistent with the
--   partial order implied by the LocAST.
sortSchemes :: LocAST -> [ConstraintScheme] -> [ConstraintScheme]
sortSchemes tree schemes = concatMap (fold alg) $ fmap (fmap fst) tree where
  -- having more than one scheme at a location only happens with mutually
  -- recursive bindings, which our support for is.... well, it doesn't
  -- crash. Not much point focusing on performance in a case that we don't
  -- handle well anyways.
  locSchemes = IM.fromListWith (++) $ map locScheme schemes
  locScheme s@(Scheme li _ _ _) = (li, [s])
  getSchemes loc = fromMaybe [] $ locSchemes IM.!? loc

  alg :: TreeF LocIndex [ConstraintScheme] -> [ConstraintScheme]
  -- include the schemes from lower down the tree before the schemes here.
  alg (NodeF loc lowerSchemes) = concat lowerSchemes ++ getSchemes loc

declareScheme :: LocAST -> ConstraintScheme -> Command
declareScheme ast (Scheme li name vars cs) =
  DeclareScheme name vars $ makeTypingAssertions [subAST] located
  where
    subAST = case findSubAST li ast of
      Just sa -> sa
      Nothing -> error "declareScheme: location was not defined"
    located = locateConstraints cs
