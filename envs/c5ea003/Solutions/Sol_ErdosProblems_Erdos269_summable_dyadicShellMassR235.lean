-- Prove2me | solution 1 for ErdosProblems.Erdos269.summable_dyadicShellMassR235
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:27:20.025259+00:00
-- url     : https://prove2.me/submissions/085829cb-b1e8-4060-a6d1-c3a6c71b7113

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Theorems.Thm_ErdosProblems_Erdos269_dyadicShellMassR235_le_majorant
import Theorems.Thm_ErdosProblems_Erdos269_dyadicShellMassR235_nonneg
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

open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution : Summable dyadicShellMassR235 := by
  have hpoly : Summable
      (fun n : ℕ => (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num)
  have hshift : Summable
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2) *
        (1 / 2 : ℝ) ^ (n + 1)) := by
    simpa only [Function.comp_apply, Nat.add_comm] using
      hpoly.comp_injective (add_right_injective 1)
  have hmajor : Summable
      (fun n : ℕ => 30 * ((((n + 1 : ℕ) : ℝ) ^ 2) *
        (1 / 2 : ℝ) ^ (n + 1))) := hshift.mul_left 30
  refine Summable.of_nonneg_of_le dyadicShellMassR235_nonneg ?_ hmajor
  exact dyadicShellMassR235_le_majorant
