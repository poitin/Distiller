module EvalTest where

import Helpers
import Test.HUnit
import Term


eval1Test :: IO Test
eval1Test = let
  c = "import Bool\n" ++
      "import QTree\n" ++
      "import Matrices\n" ++
      "main = mask (mask experiment_mask1M1 experiment_mask11) experiment_mask12;\n" ++
      "isZ x = case x of\n" ++
               "True -> False\n" ++
               "| False -> True\n" in
  case parseModule c of
    Left s -> assertFailure "Oops"
    Right (fs, d) -> do
        s <- loadProg fs [] d $ Just "examples/"
        case s of
          Nothing -> assertFailure "Ooops"
          Just (t, d) -> do
            (v, r, a) <- evalProg (free t) t d
            return $ TestList [TestCase $ assertEqual "lala" r 67, TestCase $ assertEqual "lala" a 12]