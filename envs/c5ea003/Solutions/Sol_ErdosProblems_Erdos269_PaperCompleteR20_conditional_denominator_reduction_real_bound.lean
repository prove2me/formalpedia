-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.conditional_denominator_reduction_real_bound
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:15:07.627712+00:00
-- url     : https://prove2.me/submissions/2e5a642c-1bb5-4d3f-b625-17fadc516c85

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Theorems.Thm_ErdosProblems_Erdos269_integralCarry_cancel_commonFactor
import Theorems.Thm_ErdosProblems_Erdos269_reducedIntegralCarry_window
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ErdosProblems.Erdos269.PaperCompleteR20
end ErdosProblems.Erdos269.PaperCompleteR20

/-!
# Denominator reduction with the literal real upper bound

The paper quantifies the upper-bound parameter over all reals and asserts an
equivalence. Positive common-factor cancellation preserves both directions;
no integrality of that parameter or bound function is needed.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20
theorem positive_real_bound_commonFactor_iff
    {c d s B : ℤ} (hs : 0 < s) (hfactor : c = s * d) (t : ℝ) :
    (0 < c ∧ (c : ℝ) ≤ ((s * B : ℤ) : ℝ) * t) ↔
      (0 < d ∧ (d : ℝ) ≤ (B : ℝ) * t) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  rw [hfactor]
  push_cast
  rw [mul_pos_iff_of_pos_left hs, mul_assoc, mul_le_mul_iff_right₀ hsR]
end ErdosProblems.Erdos269.PaperCompleteR20

open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
theorem solution
    (c d b m : ℕ → ℤ) (s B : ℤ) (hs : 0 < s)
    (hfactor : ∀ n, c n = s * d n)
    (hrec : ∀ n, c (n + 1) = b n * c n - (s * B) * m n) :
    (∀ n, d (n + 1) = b n * d n - B * m n) ∧
    (∀ lo len, d (lo + len) = windowBase b lo len * d lo -
      B * windowForcing b m lo len) ∧
    (∀ n (t : ℝ),
      (0 < c n ∧ (c n : ℝ) ≤ ((s * B : ℤ) : ℝ) * t) ↔
        (0 < d n ∧ (d n : ℝ) ≤ (B : ℝ) * t)) :=
  ⟨integralCarry_cancel_commonFactor c d b m s B hs.ne' hfactor hrec,
    reducedIntegralCarry_window c d b m s B hs.ne' hfactor hrec,
    fun n t => positive_real_bound_commonFactor_iff hs (hfactor n) t⟩
