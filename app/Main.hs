module Main (main) where

import Control.Monad (forM_)
import System.IO
import System.Process
import System.Environment
import System.FilePath

import Conversion
import SMT
import SMT.Response qualified as R

main :: IO ()
main = do
  args <- getArgs
  let path : _ = args
      z3mlPath = path -<.> "z3ml"
      smtPath  = path -<.> "smt"
  let cp = proc "zgen" [path, "-o", z3mlPath]
  (_, _, _, ph) <- createProcess cp
  _exitCode <- waitForProcess ph
  z3ml <- readFile z3mlPath
  let ci = getParse "zgen produced malformed z3ml" $ parseInput z3mlPath z3ml
      commands = convert ci
      rangeMap = getRangeMapping ci
  writeFile smtPath (outputCommands commands)
  let z3command = proc "z3" [smtPath]
      cp = z3command{ std_out = CreatePipe }
  (_, Just z3out, _, ph) <- createProcess cp
  _exitCode <- waitForProcess ph
  z3response <- hGetContents z3out
  hPutStrLn stderr z3response
  let (weight, badLocs) = R.process
                        $ getParse "z3 produced malformed response"
                        $ R.parse "z3<stdout>" z3response
  -- TODO: write this to a file
  putStr "weight: "
  print weight
  putStrLn "locations:"
  forM_ badLocs $ \loc ->
    putStr "  " >> print (lookupLoc loc rangeMap)

getParse :: Show e => String -> Either e a -> a
getParse msg (Left e) = error $ msg ++ ": " ++ show e
getParse _ (Right v)  = v
