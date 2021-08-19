import EvalTest

import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit

main :: IO ()
main = do
    tests <- EvalTest.eval1Test 
    defaultMainWithOpts (hUnitTestToTests tests) mempty
