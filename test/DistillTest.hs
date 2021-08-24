module DistillTest (distillerTests) where

import Helpers
import Test.HUnit
import Term
import Trans (dist)
import System.Timeout
import Data.List

defaultTimeout = 10 * 1000000

load root imports =
  do s <- loadProg [root] [] [] $ Just imports
     case s of
      Nothing -> assertFailure $ "Program loading failed for program " ++ root ++ " and imports " ++ imports ++ "."
      Just (t, d) -> return (t,d)
  

createDistillationTest fileToDistill importsForDistill fileWithGold importsForGold timeoutForDistillation =  do
  progToDistill <- load fileToDistill importsForDistill
  distillationResult <- timeout timeoutForDistillation (pure $ dist progToDistill)
  case distillationResult of
    Nothing -> assertFailure $ "Timeout in " ++ show (timeoutForDistillation `div` 1000000) ++ " seconds is expired."
    Just (mainOfDistilledProg, x) -> do
      (mainOfExpectedProg, y) <- load fileWithGold importsForGold
      let actual = ("main", ([], mainOfDistilledProg)) : x
      let expected = ("main", ([], mainOfExpectedProg)) : y
      return $ TestCase $ assertEqual ("Distilled program for " ++ fileToDistill ++ " should be equals to " ++ fileWithGold ++ ".") expected (expected `intersect` actual) 


distillerTests :: IO Test
distillerTests = do 
  test1 <- createDistillationTest "test1" "examples/" "test1_gold" "examples/" defaultTimeout
  testAppApp <- createDistillationTest "appapp" "inputs/" "gold/appapp_gold" "inputs/" defaultTimeout
  testMap <- createDistillationTest "map" "inputs/" "gold/map_gold" "inputs/" defaultTimeout
  
  return $ TestList [test1, testAppApp, testMap]
