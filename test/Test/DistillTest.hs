module Test.DistillTest where

import Helpers
import Test.Tasty
import Test.Tasty.HUnit
import Term
import Trans (dist)
import Data.List
import Data.Maybe (fromJust, isJust)
import Text.Printf ( printf )
import Control.Exception

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
  let testCaseName = printf "Distillation of %s" fileToDistill
  if isJust progToDistill
  then do
    distillationResult <- try (evaluate $ dist (fromJust progToDistill)) :: IO (Either SomeException (Term, [(String, ([String], Term))]))
    case distillationResult of
      Left ex -> do 
        let assertion = assertFailure $ printf "program: %s; imports: %s; exception: %s" fileToDistill importsForDistill (show ex)
        return $ testCase testCaseName assertion
      Right  (mainOfDistilledProg, x) -> do
        let actual = ("main", ([], mainOfDistilledProg)) : x
        let expected = ("main", ([], mainOfExpectedProg)) : y
        let assertion = expected `intersect` actual @?= expected        
        return $ timeOutTest timeoutForDistillation testCaseName assertion
  else do
    let testCaseName = printf "Parsing: %s" fileToDistill
    let assertion = assertFailure $ printf "program: %s; imports: %s." fileToDistill importsForDistill
    return $ testCase testCaseName assertion

-- Basic tests

test_distillerBasicTest1 :: IO TestTree
test_distillerBasicTest1 =
  createDistillationTest "plusassoc" "inputs/" "gold/plusassoc_gold" "inputs/" defaultTimeout

test_distillerBasicTest2 :: IO TestTree
test_distillerBasicTest2 = do
  createDistillationTest "appapp" "inputs/" "gold/appapp_gold" "inputs/" defaultTimeout

test_distillerBasicTest3 :: IO TestTree
test_distillerBasicTest3 = do
  createDistillationTest "map" "inputs/" "gold/map_gold" "inputs/" defaultTimeout

test_distillerBasicTest4 :: IO TestTree
test_distillerBasicTest4 =
  createDistillationTest "pluscomm" "inputs/" "gold/pluscomm_gold" "inputs/" defaultTimeout

test_distillerBasicTest5 :: IO TestTree
test_distillerBasicTest5 =
  createDistillationTest "revrev" "inputs/" "gold/revrev_gold" "inputs/" defaultTimeout


-- Linear algebra tests

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
