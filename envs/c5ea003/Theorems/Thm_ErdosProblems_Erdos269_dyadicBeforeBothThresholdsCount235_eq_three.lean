-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_dyadicBeforeBothThresholdsCount235_eq_three
-- name    : ErdosProblems.Erdos269.dyadicBeforeBothThresholdsCount235_eq_three
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:21:08.926372+00:00
-- url     : https://prove2.me/theorems/05a6a348-c331-44a4-9d9f-12809fc0f7e0
-- title:
--   DyadicBeforeBothThresholdsCount235 eq three
-- statement:
--   When the new 3-power threshold is no larger than the 5-power threshold, the count before both thresholds equals the count before the 3-threshold.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/DyadicBlockThresholdPartition.lean#L111-L127
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

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


open scoped BigOperators

open ErdosProblems.Erdos269

theorem ErdosProblems.Erdos269.dyadicBeforeBothThresholdsCount235_eq_three
    {a : ℕ}
    (horder : 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤
      5 ^ Nat.log 5 (2 ^ (a + 1))) :
    dyadicBeforeBothThresholdsCount235 a =
      dyadicBeforeThresholdCount235 3 a := by sorry
