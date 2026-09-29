-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_positive_integral_coefficients_of_four_agreements
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:47:24.759043+00:00
-- url     : https://prove2.me/submissions/3a28a883-35d9-4d34-8e95-f5bb03c14fbb

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_integral_coefficients_of_four_agreements
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

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (C : ℕ → ℤ) (κ η : ℚ) (hκ : 0 < κ) (n : ℕ)
    (hagree : ∀ j : ℕ, j < 4 → (C (n + j) : ℚ) =
      κ * ((n + j : ℕ) : ℚ) * (((n + j : ℕ) : ℚ) + 1) *
        (((n + j : ℕ) : ℚ) + 2) + η) :
    ∃ m c : ℤ, 0 < m ∧ (m : ℚ) = 6 * κ ∧ (c : ℚ) = η ∧
      ∀ k : ℕ, κ * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + η =
        ((m * risingBinomial k + c : ℤ) : ℚ) := by
  obtain ⟨m, c, hm, hc, heval⟩ :=
    cubic_integral_coefficients_of_four_agreements C κ η n hagree
  have hmpos : (0 : ℚ) < (m : ℚ) := by rw [hm]; positivity
  exact ⟨m, c, by exact_mod_cast hmpos, hm, hc, heval⟩
