-- Prove2me | solution 1 for ErdosProblems.Erdos269.dyadicHalfClearedMass235_eq_thresholdCounts
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:38:07.924832+00:00
-- url     : https://prove2.me/submissions/3f709628-b750-458f-a3f6-69cab695666c

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Theorems.Thm_ErdosProblems_Erdos269_oddHeightSuffix235_eq_thresholdFactors
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
# Erdős #269: all-scale internal-threshold partition

The preceding block-mass module proves that every cleared dyadic-shell term is
`2` times an odd suffix product.  Here that suffix is identified pointwise and
then summed: the only tests are whether the smooth point lies before the unique
internal `3`-power and `5`-power thresholds.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators











/-- Generic two-threshold summation identity specialized to weights `3` and
`5`. -/
theorem sum_three_five_thresholdFactors
    (s : Finset (ℕ × ℕ × ℕ)) (P Q : (ℕ × ℕ × ℕ) → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (∑ e ∈ s, (if P e then 3 else 1) * (if Q e then 5 else 1)) =
      s.card + 2 * (s.filter P).card + 4 * (s.filter Q).card +
        8 * (s.filter fun e => P e ∧ Q e).card := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert x s hx ih =>
      by_cases hP : P x <;> by_cases hQ : Q x <;>
        rw [Finset.sum_insert hx, ih] <;>
        simp [Finset.filter_insert, hx, hP, hQ] <;> omega
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution (a : ℕ) :
    dyadicHalfClearedMass235 a =
      (dyadicSmoothShell235 a).card +
        2 * dyadicBeforeThresholdCount235 3 a +
        4 * dyadicBeforeThresholdCount235 5 a +
        8 * dyadicBeforeBothThresholdsCount235 a := by
  classical
  unfold dyadicHalfClearedMass235
  rw [Finset.sum_congr rfl (fun e he => oddHeightSuffix235_eq_thresholdFactors he)]
  exact sum_three_five_thresholdFactors
    (dyadicSmoothShell235 a)
    (fun e => smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      3 ^ Nat.log 3 (2 ^ (a + 1)))
    (fun e => smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      5 ^ Nat.log 5 (2 ^ (a + 1)))
