-- Prove2me | solution 1 for SingularModuli.factor_77
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:47:36.643916+00:00
-- url     : https://prove2.me/submissions/f281d950-281d-49af-b4e9-a6f72ae5908d

import Mathlib
import Definitions.Def_Cryptography_SingularModuli_Experiments
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion
import Definitions.Def_Cryptography_SingularModuli_RootCount
import Definitions.Def_Cryptography_SingularModuli_SqrtBarrier

namespace SingularModuli

open Polynomial Finset FactoringBarriers

theorem solution : evalGcd H15 0 77 = 11 := by
  rw [evalGcd]
  simp only [H15, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  decide

end SingularModuli

open SingularModuli

theorem solution : evalGcd H15 0 77 = 11 :=
  SingularModuli.solution

#print axioms solution
