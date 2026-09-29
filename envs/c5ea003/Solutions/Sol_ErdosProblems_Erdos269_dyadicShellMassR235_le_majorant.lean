-- Prove2me | solution 1 for ErdosProblems.Erdos269.dyadicShellMassR235_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:01:37.349389+00:00
-- url     : https://prove2.me/submissions/4f27be48-c4c6-4292-8ce7-f22499831292

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Theorems.Thm_ErdosProblems_Erdos269_dyadicOrderedBlockDigit235_le_quadratic
import Theorems.Thm_ErdosProblems_Erdos269_half_threePrimeHeight_mul_dyadicShellMassR235
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: summability of the actual dyadic shell masses

The ordered source digit has a deliberately coarse quadratic majorant.  The
key point is structural: in a multiplicative interval of width two, fixing the
`3`- and `5`-exponents determines the `2`-exponent, while both odd exponents
are smaller than the dyadic scale.  This gives at most `(a+1)^2` shell points.
-/

namespace ErdosProblems.Erdos269
/-- The dyadic endpoint height contains its complete binary factor. -/
theorem pow_two_succ_le_threePrimeHeight235 (a : ℕ) :
    2 ^ (a + 1) ≤ threePrimeHeight 2 3 5 (2 ^ (a + 1)) := by
  unfold threePrimeHeight
  rw [Nat.log_pow (by norm_num : 1 < 2)]
  exact (Nat.le_mul_of_pos_right _ (by positivity)).trans
    (Nat.le_mul_of_pos_right _ (by positivity))
end ErdosProblems.Erdos269

open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution (a : ℕ) :
    dyadicShellMassR235 a ≤
      30 * (((a + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (a + 1)) := by
  let H : ℝ := threePrimeHeight 2 3 5 (2 ^ (a + 1))
  let d : ℝ := dyadicOrderedBlockDigit235 a
  have hHpos : 0 < H := by
    dsimp [H]
    norm_num [threePrimeHeight]
  have hmass := half_threePrimeHeight_mul_dyadicShellMassR235 a
  have hmassEq : dyadicShellMassR235 a = 2 * d / H := by
    apply (eq_div_iff (ne_of_gt hHpos)).2
    dsimp [H, d] at hmass ⊢
    field_simp at hmass
    nlinarith
  have hd : d ≤ 15 * (((a + 1 : ℕ) : ℝ) ^ 2) := by
    dsimp [d]
    exact_mod_cast dyadicOrderedBlockDigit235_le_quadratic a
  have hH : (2 : ℝ) ^ (a + 1) ≤ H := by
    dsimp [H]
    exact_mod_cast pow_two_succ_le_threePrimeHeight235 a
  rw [hmassEq]
  calc
    2 * d / H ≤ 2 * (15 * (((a + 1 : ℕ) : ℝ) ^ 2)) / H := by
      exact div_le_div_of_nonneg_right (by nlinarith) hHpos.le
    _ ≤ 2 * (15 * (((a + 1 : ℕ) : ℝ) ^ 2)) / (2 : ℝ) ^ (a + 1) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hH
    _ = 30 * (((a + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (a + 1)) := by
      rw [one_div_pow]
      ring
