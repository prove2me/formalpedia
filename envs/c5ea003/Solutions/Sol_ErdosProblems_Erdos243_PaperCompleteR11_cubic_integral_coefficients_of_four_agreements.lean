-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_integral_coefficients_of_four_agreements
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:43:25.475608+00:00
-- url     : https://prove2.me/submissions/1238bbd5-8eee-4c0e-98d6-9e0618ba3357

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_six_mul_risingBinomial
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
    (C : ℕ → ℤ) (κ η : ℚ) (n : ℕ)
    (hagree : ∀ j : ℕ, j < 4 → (C (n + j) : ℚ) =
      κ * ((n + j : ℕ) : ℚ) * (((n + j : ℕ) : ℚ) + 1) *
        (((n + j : ℕ) : ℚ) + 2) + η) :
    ∃ m c : ℤ, (m : ℚ) = 6 * κ ∧ (c : ℚ) = η ∧
      ∀ k : ℕ, κ * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + η =
        ((m * risingBinomial k + c : ℤ) : ℚ) := by
  let m : ℤ := C (n + 3) - 3 * C (n + 2) + 3 * C (n + 1) - C n
  have h0 := hagree 0 (by decide)
  have h1 := hagree 1 (by decide)
  have h2 := hagree 2 (by decide)
  have h3 := hagree 3 (by decide)
  simp only [Nat.add_zero] at h0
  push_cast at h1 h2 h3
  have hm : (m : ℚ) = 6 * κ := by
    dsimp [m]
    push_cast
    linear_combination h3 - 3 * h2 + 3 * h1 - h0
  let c : ℤ := C n - m * risingBinomial n
  have hc : (c : ℚ) = η := by
    have hb : (6 : ℚ) * (risingBinomial n : ℚ) =
        (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) := by
      exact_mod_cast six_mul_risingBinomial n
    dsimp [c]
    push_cast
    rw [hm]
    linear_combination h0 - κ * hb
  refine ⟨m, c, hm, hc, ?_⟩
  intro k
  have hb : (6 : ℚ) * (risingBinomial k : ℚ) =
      (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) := by
    exact_mod_cast six_mul_risingBinomial k
  push_cast
  rw [hm, hc]
  linear_combination -κ * hb
