module Test.DistillTest where

import Helpers
import Test.Tasty
import Test.Tasty.HUnit
import Term
import Trans (dist)
import System.Timeout
import Data.List
import Data.Maybe (fromJust, isJust)
import Text.Printf ( printf )

defaultTimeout :: Integer
defaultTimeout = 2000000

timeOutTest :: Integer -> TestName -> Assertion -> TestTree
timeOutTest timeout testName assertion =
  localOption (mkTimeout timeout) $ testCase testName assertion

load :: String -> String -> IO (Maybe (Term, [(String, ([String], Term))]))
load root imports = loadProg [root] [] [] $ Just imports

createDistillationTest :: String -> String -> String -> String -> Integer -> IO TestTree
createDistillationTest fileToDistill importsForDistill fileWithGold importsForGold timeoutForDistillation =  do
  progToDistill <- load fileToDistill importsForDistill
  (mainOfExpectedProg, y) <- fromJust <$> load fileWithGold importsForGold -- parsing golden file should always succeed
  if isJust progToDistill
  then do
    let (mainOfDistilledProg, x) = dist (fromJust progToDistill)
    let actual = ("main", ([], mainOfDistilledProg)) : x
    let expected = ("main", ([], mainOfExpectedProg)) : y
    let assertion = expected `intersect` actual @?= expected
    let testCaseName = printf "Distillation: %s" fileToDistill
    return $ timeOutTest timeoutForDistillation testCaseName assertion
  else do
    let testCaseName = printf "Parsing: %s" fileToDistill
    let assertion = isJust progToDistill @? printf "program: %s; imports: %s." fileToDistill importsForDistill
    return $ testCase testCaseName assertion

test_distillerBasicTest1 :: IO TestTree
test_distillerBasicTest1 =
  createDistillationTest "test1" "examples/" "test1_gold" "examples/" defaultTimeout

test_distillerBasicTest2 :: IO TestTree
test_distillerBasicTest2 = do
  createDistillationTest "appapp" "inputs/" "gold/appapp_gold" "inputs/" defaultTimeout

test_distillerBasicTest3 :: IO TestTree
test_distillerBasicTest3 = do
  createDistillationTest "map" "inputs/" "gold/map_gold" "inputs/" defaultTimeout

test_distillerLinearAlgebraTest1 :: IO TestTree
test_distillerLinearAlgebraTest1 = do
  createDistillationTest "linearAlgebraTests/addadd" "inputs/" "gold/linearAlgebra/addadd_gold" "inputs/" defaultTimeout

test_distillerLinearAlgebraTest2 :: IO TestTree
test_distillerLinearAlgebraTest2 = do
  createDistillationTest "linearAlgebraTests/addmask" "inputs/" "gold/linearAlgebra/addmask_gold" "inputs/" defaultTimeout

test_distillerLinearAlgebraTest3 :: IO TestTree
test_distillerLinearAlgebraTest3 = do
  createDistillationTest "linearAlgebraTests/multmask" "inputs/" "gold/linearAlgebra/multmask_gold" "inputs/" defaultTimeout

test_distillerLinearAlgebraTest4 :: IO TestTree
test_distillerLinearAlgebraTest4 = do
  createDistillationTest "linearAlgebraTests/kronmask" "inputs/" "gold/linearAlgebra/kronmask_gold" "inputs/" defaultTimeout