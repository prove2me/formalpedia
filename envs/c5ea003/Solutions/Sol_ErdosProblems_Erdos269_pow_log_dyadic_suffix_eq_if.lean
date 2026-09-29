-- Prove2me | solution 1 for ErdosProblems.Erdos269.pow_log_dyadic_suffix_eq_if
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:22:33.490537+00:00
-- url     : https://prove2.me/submissions/fbcdef35-ce68-45aa-a013-76125699cb4d

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Theorems.Thm_ErdosProblems_Erdos269_log_dyadic_succ_le
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
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {p a x : ℕ} (hp : 2 ≤ p) (hx : 0 < x)
    (hlower : 2 ^ a ≤ x) (hupper : x < 2 ^ (a + 1)) :
    p ^ (Nat.log p (2 ^ (a + 1)) - Nat.log p x) =
      if x < p ^ Nat.log p (2 ^ (a + 1)) then p else 1 := by
  have hpOne : 1 < p := lt_of_lt_of_le (by norm_num) hp
  have hlogLower : Nat.log p (2 ^ a) ≤ Nat.log p x :=
    Nat.log_mono_right hlower
  have hlogUpper : Nat.log p x ≤ Nat.log p (2 ^ (a + 1)) :=
    Nat.log_mono_right hupper.le
  have hstep := log_dyadic_succ_le (a := a) hp
  by_cases hthreshold : x < p ^ Nat.log p (2 ^ (a + 1))
  · have hlt : Nat.log p x < Nat.log p (2 ^ (a + 1)) :=
      (Nat.log_lt_iff_lt_pow hpOne (Nat.ne_of_gt hx)).2 hthreshold
    have hdiff : Nat.log p (2 ^ (a + 1)) - Nat.log p x = 1 := by omega
    simp [hthreshold, hdiff]
  · have hnlt : ¬ Nat.log p x < Nat.log p (2 ^ (a + 1)) := by
      intro hlt
      exact hthreshold ((Nat.log_lt_iff_lt_pow hpOne (Nat.ne_of_gt hx)).1 hlt)
    have heq : Nat.log p x = Nat.log p (2 ^ (a + 1)) := by omega
    simp [hthreshold, heq]
