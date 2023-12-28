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
import Data.List (foldl', partition, sortOn)

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
type LocAST = Forest (LocIndex, Maybe Int)

recoverAST :: [(LocIndex, Range, Maybe Int)] -> LocAST
recoverAST = fmap (fmap removeRange) . sortAST . foldl' insertF []
  where
    insertF :: Forest (Int, Range, Maybe Int)
            -> (Int, Range, Maybe Int)
            -> Forest (Int, Range, Maybe Int)
    insertF [] p = [new p]
    insertF (t : ts) p@(_,r,_)
      | r `contains` tr =
        let (cs, ts') = partition ((r `contains`) . range) (t:ts)
        in Node p cs : ts'
      | tr `contains` r = insertT t p : ts
      | otherwise = t : insertF ts p
      where 
        range = proj2 . rootLabel
        proj2 (_,x,_) = x
        tr = range t

    insertT :: Tree (Int, Range, Maybe Int)
            -> (Int, Range, Maybe Int)
            -> Tree (Int, Range, Maybe Int)
    insertT (Node tr cf) p = Node tr $ insertF cf p

    new x = Node x []

    removeRange (ix,_,w) = (ix, w)

sortAST :: Forest (Int, Range, Maybe Int) -> Forest (Int, Range, Maybe Int)
sortAST = fmap sortChildren . sortOn (\(Node (_,r,_) _) -> r) where
  sortChildren (Node p cs) = Node p $ sortAST cs

findSubAST :: Int -> LocAST -> Maybe (Tree (LocIndex, Maybe Int))
findSubAST needle haystack = case haystack of
  [] -> Nothing
  t@(Node root sast) : trs
    | needle == fst root -> Just t
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
