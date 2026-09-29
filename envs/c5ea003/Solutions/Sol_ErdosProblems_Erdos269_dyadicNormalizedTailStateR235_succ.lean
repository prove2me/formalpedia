-- Prove2me | solution 1 for ErdosProblems.Erdos269.dyadicNormalizedTailStateR235_succ
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:10:25.62398+00:00
-- url     : https://prove2.me/submissions/9c616f6d-a6a8-46c5-9615-55439a20ea3e

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Theorems.Thm_ErdosProblems_Erdos269_half_threePrimeHeight_mul_dyadicShellMassR235
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight_dyadicBlock_succ
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
theorem solution
    (tail : ℕ → ℝ)
    (htail : ∀ a, tail a = dyadicShellMassR235 a + tail (a + 1))
    (a : ℕ) :
    dyadicNormalizedTailStateR235 tail (a + 1) =
      dyadicBlockBase235 a * dyadicNormalizedTailStateR235 tail a -
        dyadicOrderedBlockDigit235 a := by
  have hheight := threePrimeHeight_dyadicBlock_succ a
  have hheightR :
      (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) =
        dyadicBlockBase235 a * threePrimeHeight 2 3 5 (2 ^ a) := by
    exact_mod_cast hheight
  have hmass := half_threePrimeHeight_mul_dyadicShellMassR235 a
  unfold dyadicNormalizedTailStateR235
  rw [hheightR]
  rw [hheightR] at hmass
  rw [htail a]
  linarith
