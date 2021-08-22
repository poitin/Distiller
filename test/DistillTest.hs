module DistillTest (distill1Test) where

import Helpers
import Test.HUnit
import Term
import Trans (dist)

distill1Test :: IO Test
distill1Test = let
  c = "import Bool\n" ++
      "import QTree\n" ++
      "import Matrices\n" ++
      "main = kron (not) (or) (mask m1 msk) (m2)\n" in
  case parseModule c of
    Left s -> assertFailure "Oops"
    Right (fs, d) -> do
        s <- loadProg fs [] d $ Just "examples/"
        case s of
          Nothing -> assertFailure "Ooops"
          Just (t, d) -> do
            expectedProg' <- expectedProg
            return $ TestList [TestCase $ assertEqual "lala" expectedProg' (showProg $ dist (t,d))]
            
expectedProg :: IO String
expectedProg = readFile "examples/MasksDistilled.pot"