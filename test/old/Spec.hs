module Spec where

import EvalTest
import DistillTest

import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit

main :: IO ()
main = do
    evalTests <- EvalTest.eval1Test
    distilledBasicTests <- DistillTest.distillerBasicTests
    distilledLinearAlgebraTests <- DistillTest.distillerLinearAlgebraTests
    let distillEvalTests = []
    defaultMainWithOpts (hUnitTestToTests $ TestList $ evalTests : distilledBasicTests : distilledLinearAlgebraTests : distillEvalTests) mempty
