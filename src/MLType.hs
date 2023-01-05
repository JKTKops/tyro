{-# LANGUAGE InstanceSigs #-}
module MLType where

import Pretty
import Data.List.NonEmpty ( NonEmpty(..) )
import Data.Set qualified as S
import ParserUtils ((<|>))
import ParserUtils qualified as P

data TyVar = TV String (Maybe Int)
  deriving (Eq, Ord, Show)

data Type
  = TyCon String [Type]
  | TyArr Type Type
  | TyTup (NonEmpty Type)
  | TyVar TyVar
  deriving (Eq, Ord, Show)


type FreeVars = S.Set TyVar
typeFvs :: Type -> FreeVars
typeFvs (TyCon _ ts) = S.unions $ map typeFvs ts
typeFvs (TyArr t1 t2) = typeFvs t1 `S.union` typeFvs t2
typeFvs (TyTup ts) = S.unions $ fmap typeFvs ts
typeFvs (TyVar tv) = S.singleton tv

instance Pretty TyVar where
  pretty :: TyVar -> String
  pretty (TV n Nothing) = "-" ++ n
  pretty (TV n (Just i)) = "-" ++ n ++ "." ++ show i

instance Pretty Type where
  prettyPrec :: Int -> Type -> ShowS
  prettyPrec  n (TyVar tv) = prettyPrec n tv
  prettyPrec _n (TyCon name []) = showString name
  prettyPrec  n (TyCon name ts)
    = showParen (n > 10)
        ( showString name
        . foldr (\t f -> showChar ' ' . prettyPrec 10 t . f) id ts
        )
  prettyPrec n (TyArr l r)
    = showParen (n > 0) $ 
        prettyPrec 4 l . showString " -> " . prettyPrec 0 r
  prettyPrec _n (TyTup (t :| ts))
    = showParen True $
        prettyPrec 4 t
        . foldr (\ty f -> showString " * " . prettyPrec 4 ty . f) id ts

parseTyVar :: P.Parser TyVar
parseTyVar = P.lexeme $ do
  name <- P.char '\'' *> P.ident
  uniq <- P.optionMaybe $ P.char '.' *> P.int
  return $ TV name uniq

parseName :: P.Parser String
parseName = P.lexeme P.ident

parsePType :: P.Parser Type
parsePType
      -- this gets precedence wrong in some cases. TODO
  =   P.parens (handleTup <$> parseType <*> P.many (star *> parseType))
  <|> (TyVar <$> parseTyVar)
  <|> (flip TyCon [] <$> parseName)
  where
    star = P.lexeme $ P.char '*'
    handleTup ty [] = ty
    handleTup ty ts = TyTup (ty :| ts)

parseType :: P.Parser Type
parseType = do
  p1 <- parsePType
  P.optionMaybe parseName >>= \case
    Just n -> pure $ TyCon n [p1]
    Nothing -> P.optionMaybe (P.lexeme $ P.string "->") >>= \case
      Just{}  -> TyArr p1 <$> parsePType
      Nothing -> pure p1

