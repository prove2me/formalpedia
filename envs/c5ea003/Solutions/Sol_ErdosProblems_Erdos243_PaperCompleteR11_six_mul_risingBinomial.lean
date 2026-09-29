-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.six_mul_risingBinomial
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:50:54.911489+00:00
-- url     : https://prove2.me/submissions/46a2377f-0a00-41bf-9591-bf0568617880

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Mathlib
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Integral normalisation at the quarter-density threshold

The integral coefficients are
constructed from one clean four-window. In particular they are conclusions,
not hidden hypotheses in an arbitrary rational-profile statement.
- A non-integral constant or non-integral third difference gives density >= 1/4.
- The argument needs only an integer-valued sequence, not a recurrence.
- No claim that an integral constant must be +1 or -1 is made here.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11
/-- The factor six is exact, including at the first two indices. -/
theorem six_mul_rising_choose (n : ℕ) :
    6 * (n + 2).choose 3 = n * (n + 1) * (n + 2) := by
  have h1 : (n + 1) * n = (n + 1).choose 2 * 2 := by
    simpa using Nat.add_one_mul_choose_eq n 1
  have h2 : (n + 2) * (n + 1).choose 2 = (n + 2).choose 3 * 3 := by
    simpa only [Nat.add_assoc] using Nat.add_one_mul_choose_eq (n + 1) 2
  have h3 := congrArg (fun t : ℕ ↦ t * (n + 2)) h1
  nlinarith
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution (n : ℕ) :
    6 * risingBinomial n = (n : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 2) := by
  have h := six_mul_rising_choose n
  unfold risingBinomial
  exact_mod_cast h
