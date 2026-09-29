-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_oddHeightSuffix235_eq_thresholdFactors
-- name    : ErdosProblems.Erdos269.oddHeightSuffix235_eq_thresholdFactors
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:21:27.123726+00:00
-- url     : https://prove2.me/theorems/07dc8a08-f4d2-4791-ad83-e7d54766064a
-- title:
--   OddHeightSuffix235 eq thresholdFactors
-- statement:
--   For a point of the dyadic 2·3·5 shell, its odd height suffix is the product of a 3-or-1 factor and a 5-or-1 factor selected by their pure-power thresholds.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/DyadicBlockThresholdPartition.lean#L42-L55
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

theorem ErdosProblems.Erdos269.oddHeightSuffix235_eq_thresholdFactors
    {a : ℕ} {e : ℕ × ℕ × ℕ} (he : e ∈ dyadicSmoothShell235 a) :
    oddHeightSuffix235 a e =
      (if smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
          3 ^ Nat.log 3 (2 ^ (a + 1)) then 3 else 1) *
      (if smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
          5 ^ Nat.log 5 (2 ^ (a + 1)) then 5 else 1) := by sorry
