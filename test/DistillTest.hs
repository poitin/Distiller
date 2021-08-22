module DistillTest where

import Helpers
import Test.HUnit
import Term
import Trans (dist)

{---distill1Test :: IO Test
distill1Test = let
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
          Just (t, d) -> let
            actualProg = showProg $ dist (t, d)
            in return $ TestList [TestCase $ assertEqual "lala" expectedProg actualProg] --}
            
--expectedProg :: String
--expectedProg =             