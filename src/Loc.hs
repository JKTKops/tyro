{-# LANGUAGE DerivingStrategies, GeneralisedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ImportQualifiedPost #-}
module Loc where

import Data.Tree
import Data.List (foldl', partition)

import ParserUtils qualified as P

-- TODO: location ranges, [(Int, Loc)] -> Tree Int
newtype Line = Line Int
  deriving newtype (Eq, Ord, Show, Num)

newtype Col = Col Int
  deriving newtype (Eq, Ord, Show, Num)

data Loc = Loc Line Col
  deriving (Eq, Ord)

instance Show Loc where
  show :: Loc -> String
  show (Loc l c) = show l ++ ";" ++ show c

data Range = Range Loc Loc
  deriving (Eq, Ord)

instance Show Range where
  show :: Range -> String
  show (Range s e) = show s ++ "-" ++ show e

disjoint :: Range -> Range -> Bool
disjoint (Range s1 e1) (Range s2 e2)
  = (s2 > e1) || (s1 > e2)

contains :: Range -> Range -> Bool
contains (Range s1 e1) (Range s2 e2)
  = s1 <= s2 && e1 >= e2

type LocAST = Forest Int

recoverAST :: [(Int, Range)] -> Forest Int
recoverAST = fmap (fmap fst) . foldl' insertF []
  where
    insertF :: Forest (Int, Range) -> (Int, Range) -> Forest (Int, Range)
    insertF [] p = [new p]
    insertF (t : ts) p@(_,r)
      | r `contains` tr =
        let (cs, ts') = partition ((r `contains`) . range) (t:ts)
        in Node p cs : ts'
      | tr `contains` r = insertT t p : ts
      | otherwise = t : insertF ts p
      where 
        range = snd . rootLabel
        tr = range t

    insertT :: Tree (Int, Range) -> (Int, Range) -> Tree (Int, Range)
    insertT (Node tr cf) p = Node tr $ insertF cf p

    new x = Node x []

parseLoc :: P.Parser Loc
parseLoc = do
  l <- P.int
  _ <- P.char ';'
  c <- P.int
  return $ Loc (Line l) (Col c)

parseRange :: P.Parser Range
parseRange = Range <$> parseLoc <*> (P.char '-' *> parseLoc)
