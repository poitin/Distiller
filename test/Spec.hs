import EvalTest
import DistillTest

import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit

main :: IO ()
main = do
    evalTests <- EvalTest.eval1Test
    distillTests <- DistillTest.distillerTests
    let distillEvalTests = []
    defaultMainWithOpts (hUnitTestToTests $ TestList $ evalTests : distillTests : distillEvalTests) mempty
