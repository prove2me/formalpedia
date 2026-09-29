-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
-- name    : ErdosProblems_Erdos269_DyadicBlockThresholdPartition
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:13:28.494758+00:00
-- url     : https://prove2.me/theorems/9f1040e0-e2b3-44cc-aa25-b00a1303901a
-- title:
--   DyadicBlockThresholdPartition
-- statement:
--   Defines the half-cleared shell mass, counts before the 3- and 5-power thresholds and before both, and the ordered block digit chosen according to the threshold order.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/DyadicBlockThresholdPartition.lean#L1-L175
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
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





/-- The half-height-cleared mass of the actual dyadic smooth shell. -/
def dyadicHalfClearedMass235 (a : ℕ) : ℕ :=
  ∑ e ∈ dyadicSmoothShell235 a, oddHeightSuffix235 a e

/-- Number of shell points before the new `p`-power threshold. -/
def dyadicBeforeThresholdCount235 (p a : ℕ) : ℕ :=
  ((dyadicSmoothShell235 a).filter fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      p ^ Nat.log p (2 ^ (a + 1))).card

/-- Number of shell points lying before both odd-channel thresholds. -/
def dyadicBeforeBothThresholdsCount235 (a : ℕ) : ℕ :=
  ((dyadicSmoothShell235 a).filter fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
        3 ^ Nat.log 3 (2 ^ (a + 1)) ∧
      smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
        5 ^ Nat.log 5 (2 ^ (a + 1))).card









/-- The source-faithful ordered block digit.  Its coefficients are the suffix
products from processing the later odd jump first: `10,4` when the `3`-jump
precedes the `5`-jump, and `2,12` in the reverse order. -/
def dyadicOrderedBlockDigit235 (a : ℕ) : ℕ :=
  if 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤ 5 ^ Nat.log 5 (2 ^ (a + 1)) then
    (dyadicSmoothShell235 a).card +
      10 * dyadicBeforeThresholdCount235 3 a +
      4 * dyadicBeforeThresholdCount235 5 a
  else
    (dyadicSmoothShell235 a).card +
      2 * dyadicBeforeThresholdCount235 3 a +
      12 * dyadicBeforeThresholdCount235 5 a



end ErdosProblems.Erdos269


