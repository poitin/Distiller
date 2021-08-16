module EvalTest where

import Test.HUnit
import Term


eval1Test :: Test
eval1Test = let
  c = ["import Bool", "import Matrices", "import QTree", "main = kron (not) (or) (mask m1 msk) (m2)"]
  in show c

-- take program main with imports in string array representation
-- fix imports => can load imports from folder with libs,
-- check eval works on given program