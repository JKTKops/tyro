module SMT.Response (parse, process) where

import Data.Functor

import ParserUtils (Parser, (<|>))
import ParserUtils qualified as P
import SMT (LocVar(..))
import Data.Char (isSpace)
import Data.Maybe (fromJust)

data Response
  = Sat | Unsat
  | Objectives Int -- conceptually Objectives Weight
  | Model [(LocVar, Bool)]
  | Stats [(String, Double)]
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
parenResponse = P.parens (
  fmap Objectives objectives <|>
  fmap Model model <|>
  fmap Stats stats)

objectives :: Parser Int
objectives = do 
  () <- exact "objectives"
  P.parens P.int

model :: Parser [(LocVar, Bool)]
model = P.many1 model1 where
  model1 = P.parens $ (,) <$> locVar <*> boolVal

stats :: Parser [(String, Double)]
stats = P.many1 field1 where
  field1 = (,) <$> fieldName <*> fieldVal
  fieldName = P.lexeme $ P.char ':' >> P.many1 (P.satisfy (not . isSpace))
  fieldVal  = P.lexeme P.double

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
--   and also the time.
-- Responses are expected in exactly the order:
-- Satness, Objectives, Model, statistics.
-- An error is raised if Unsat.
process :: [Response] -> (Int, [LocVar], Double)
process [] = error "process should be given responses directly from the parser"
process (sat : resps)
  | Sat   <- sat = case resps of
      [obj, mod, stats]
        | Objectives weight <- obj
        , Model asgn <- mod
        , Stats fields <- stats
        -> (weight, getLocs asgn, getTime fields)
      _          -> malformed "'sat' "
  | Unsat <- sat = error "z3 returned 'unsat'"
  | otherwise = malformed ""
  where
    getLocs = map fst . filter (not . snd)
    getTime = fromJust . lookup "time"
    malformed s = error $ "malformed "++s++"output from queries to z3"
