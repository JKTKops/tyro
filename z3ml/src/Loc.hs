{-# LANGUAGE DerivingStrategies, GeneralisedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
module Loc
  ( Line, Col, Loc, Range
  , LocIndex, LocAST
  , recoverAST, findSubAST
  , parseRange, locIndex
  ) where

import Control.Applicative ((<|>))
import Data.Tree
import Data.List (foldl', partition)

import ParserUtils qualified as P

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

type LocIndex = Int
type LocAST = Forest LocIndex

recoverAST :: [(LocIndex, Range)] -> Forest LocIndex
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

findSubAST :: Int -> LocAST -> Maybe (Tree LocIndex)
findSubAST needle haystack = case haystack of
  [] -> Nothing
  t@(Node root sast) : trs
    | needle == root -> Just t
    | otherwise -> findSubAST needle sast <|> findSubAST needle trs

parseLoc :: P.Parser Loc
parseLoc = do
  l <- P.int
  _ <- P.char ';'
  c <- P.int
  return $ Loc (Line l) (Col c)

parseRange :: P.Parser Range
parseRange = Range <$> parseLoc <*> (P.char '-' *> parseLoc)

locIndex :: P.Parser LocIndex
locIndex = P.int
