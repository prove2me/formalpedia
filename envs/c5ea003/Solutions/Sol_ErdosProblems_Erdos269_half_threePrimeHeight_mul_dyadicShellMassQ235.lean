-- Prove2me | solution 1 for ErdosProblems.Erdos269.half_threePrimeHeight_mul_dyadicShellMassQ235
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:15:19.085864+00:00
-- url     : https://prove2.me/submissions/0f1d090a-7b4f-4333-a183-dd293081eb94

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Theorems.Thm_ErdosProblems_Erdos269_dyadicHalfClearedMass235_eq_orderedBlockDigit235
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight_dyadicShell_factor_two
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
# Erdős #269: the ordered source digit is the actual tail digit

The half-open dyadic shell has already been partitioned at the unique new
`3`- and `5`-power thresholds. This module performs the remaining source-to-
carry normalization. Clearing the literal reciprocal height mass of the shell
by half of the next endpoint height gives exactly the ordered block digit.
Consequently every tail satisfying the literal shell decomposition obeys the
affine recurrence consumed by the bounded-radix escape theorem.

No rationality or irrationality hypothesis is used here. The remaining
producer is arithmetic escape (or an exact integral tail) for this now
source-identified orbit.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution (a : ℕ) :
    ((threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) / 2) *
        dyadicShellMassQ235 a =
      dyadicOrderedBlockDigit235 a := by
  unfold dyadicShellMassQ235
  rw [Finset.mul_sum]
  calc
    ∑ e ∈ dyadicSmoothShell235 a,
        ((threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) / 2) *
          ((threePrimeHeight 2 3 5
            (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹) =
      ∑ e ∈ dyadicSmoothShell235 a, (oddHeightSuffix235 a e : ℚ) := by
        apply Finset.sum_congr rfl
        intro e he
        have hfactor := threePrimeHeight_dyadicShell_factor_two he
        have hfactorQ :
            (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) =
              2 * oddHeightSuffix235 a e *
                threePrimeHeight 2 3 5
                  (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) := by
          exact_mod_cast hfactor
        rw [hfactorQ]
        have hheight :
            (threePrimeHeight 2 3 5
              (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ) ≠ 0 := by
          norm_num [threePrimeHeight]
        field_simp
    _ = (dyadicHalfClearedMass235 a : ℚ) := by
      norm_cast
    _ = dyadicOrderedBlockDigit235 a := by
      exact_mod_cast dyadicHalfClearedMass235_eq_orderedBlockDigit235 a
