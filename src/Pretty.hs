module Pretty where

-- TODO: a -> prettyprinter.Pretty.Doc
class Pretty a where
  pretty :: a -> String
  prettyPrec :: Int -> a -> ShowS

  pretty x = prettyPrec 0 x ""
  prettyPrec _ x = (pretty x ++)
  {-# MINIMAL pretty | prettyPrec #-}
