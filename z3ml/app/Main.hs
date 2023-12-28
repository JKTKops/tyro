module Main (main) where

import Control.Monad (forM_, unless, when)
import Numeric (showFFloat)
import System.IO
import System.Process
import System.Environment
import System.Exit
import System.FilePath

import Conversion
import SMT
import SMT.Response qualified as R

main :: IO ()
main = do
  args <- getArgs
  let path : args0 = args
      (dump, args1) = case args0 of ("-d":a1) -> (True, a1) ; _ -> (False, args0)
      outPath = case args1 of ("-o":op:_) -> op ; _ -> path -<.> "z3ml.out"
      z3mlPath = path -<.> "z3ml"
      smtPath  = path -<.> "smt"
  let cp = proc "zgen" [path] -- , "-o", z3mlPath]
  (_, Just zgenOut, _, ph) <- createProcess cp{ std_out = CreatePipe }
  z3ml <- hGetContents zgenOut
  let z3ml' = unlines . drop 2 $ lines z3ml -- drop the [WRN coretys ...]
  length z3ml' `seq` pure () -- force z3ml' to avoid deadlock
  when dump $ writeFile z3mlPath z3ml'
  exitCode <- waitForProcess ph
  let ci = getParse "zgen produced malformed z3ml" $ parseInput "<zgen>" z3ml'
      commands = convert ci
      rangeMap = getRangeMapping ci
  writeFile smtPath (outputCommands commands)
  let z3command = shell $ unwords ["timeout", "90s", "z3", smtPath]
      cp = z3command{ std_out = CreatePipe }
  (_, Just z3out, _, ph) <- createProcess cp
  z3response <- hGetContents z3out
  length z3response `seq` pure ()
  exitCode <- waitForProcess ph
  exitIfFail exitCode
  --unless silent $ hPutStrLn stderr z3response
  let (weight, badLocs, time) = 
        R.process $ getParse "z3 produced malformed response"
                  $ R.parse "z3<stdout>" z3response
  withFile outPath WriteMode $ \hdl -> do
    hPutStr hdl "weight: "
    hPrint hdl weight
    hPutStr hdl "time: "
    hPutStrLn hdl $ showFFloat (Just 2) time ""
    hPutStrLn hdl "locations:"
    forM_ badLocs $ \loc ->
      hPutStr hdl "  " >> hPrint hdl (lookupLoc loc rangeMap)
  -- also echo to stdout because why not?
  -- unless silent $ readFile outPath >>= putStrLn

getParse :: Show e => String -> Either e a -> a
getParse msg (Left e) = error $ msg ++ ": " ++ show e
getParse _ (Right v)  = v

exitIfFail :: ExitCode -> IO ()
exitIfFail ExitSuccess = pure ()
exitIfFail other = exitWith other
