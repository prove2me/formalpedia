-- Prove2me | solution 1 for ErdosProblems.Erdos269.dyadicBeforeBothThresholdsCount235_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:21:16.842092+00:00
-- url     : https://prove2.me/submissions/65fe32f3-d075-4adb-be92-aa2728075ff5

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
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
    {a : ℕ}
    (horder : 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤
      5 ^ Nat.log 5 (2 ^ (a + 1))) :
    dyadicBeforeBothThresholdsCount235 a =
      dyadicBeforeThresholdCount235 3 a := by
  unfold dyadicBeforeBothThresholdsCount235 dyadicBeforeThresholdCount235
  apply congrArg Finset.card
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, hthree, -⟩
    exact ⟨he, hthree⟩
  · rintro ⟨he, hthree⟩
    exact ⟨he, hthree, lt_of_lt_of_le hthree horder⟩
