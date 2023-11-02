module SMT.Response (parse, process) where

import Data.Functor

import ParserUtils (Parser, (<|>))
import ParserUtils qualified as P
import SMT (LocVar(..))

data Response
  = Sat | Unsat
  | Objectives Int -- conceptually Objectives Weight
  | Model [(LocVar, Bool)]
  deriving (Eq, Show)

--------------------------------------------------------------------
-- Parsing Responses
--------------------------------------------------------------------

parse :: P.SourceName -> String -> Either P.ParseError [Response]
parse = P.parse (P.many1 response)

exact :: String -> Parser ()
exact s = P.lexeme $ P.string s $> ()

response :: Parser Response
response = sat <|> unsat <|> parenResponse

sat, unsat :: Parser Response
sat   = exact "sat"   $> Sat
unsat = exact "unsat" $> Unsat

parenResponse :: Parser Response
parenResponse = P.parens (fmap Objectives objectives <|> fmap Model model)

objectives :: Parser Int
objectives = do 
  () <- exact "objectives"
  P.parens P.int

model :: Parser [(LocVar, Bool)]
model = P.many1 model1 where
  model1 = P.parens $ (,) <$> locVar <*> boolVal

locVar :: Parser LocVar
locVar = P.lexeme $ LocVar <$> (P.char 'T' >> P.int)

boolVal :: Parser Bool
boolVal = P.lexeme $ true <|> false where
  true  = exact "true"  $> True
  false = exact "false" $> False

-------------------------------------------------------------------------------
-- Processing Responses
-------------------------------------------------------------------------------

-- | Process a list of responses to uncover the weight
--   and the LocVars that have been assigned False.
-- Responses are expected in exactly the order:
-- Satness, Objectives, Model.
-- An error is raised if Unsat.
process :: [Response] -> (Int, [LocVar])
process [] = error "process should be given responses directly from the parser"
process (sat : resps)
  | Sat   <- sat = case resps of
      [obj, mod] | Objectives weight <- obj
                 , Model asgn <- mod
                 -> (weight, getLocs asgn)
      _          -> malformed "'sat' "
  | Unsat <- sat = error "z3 returned 'unsat'"
  | otherwise = malformed ""
  where
    getLocs = map fst . filter (not . snd)
    malformed s = error $ "malformed "++s++"output from queries to z3"
