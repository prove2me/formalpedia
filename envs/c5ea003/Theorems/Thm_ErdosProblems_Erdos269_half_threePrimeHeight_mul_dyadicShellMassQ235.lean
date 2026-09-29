-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_half_threePrimeHeight_mul_dyadicShellMassQ235
-- name    : ErdosProblems.Erdos269.half_threePrimeHeight_mul_dyadicShellMassQ235
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T19:01:58.643292+00:00
-- url     : https://prove2.me/theorems/274e6c5d-3c87-407d-a1d4-8e4297125a36
-- title:
--   Half threePrimeHeight mul dyadicShellMassQ235
-- statement:
--   Half the next-endpoint three-prime height times the rational shell mass equals the ordered block digit.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/DyadicOrderedTailRecurrence.lean#L29-L61
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
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


open scoped BigOperators

open ErdosProblems.Erdos269

theorem ErdosProblems.Erdos269.half_threePrimeHeight_mul_dyadicShellMassQ235 (a : ℕ) :
    ((threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) / 2) *
        dyadicShellMassQ235 a =
      dyadicOrderedBlockDigit235 a := by sorry
