-- Prove2me | solution 1 for ErdosProblems.Erdos269.dyadicOrderedBlockDigit235_le_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:54:43.431984+00:00
-- url     : https://prove2.me/submissions/f14f4ad0-162f-4696-a5c5-0259d32d34d2

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Theorems.Thm_ErdosProblems_Erdos269_dyadicSmoothShell235_card_le_square
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

namespace ErdosProblems.Erdos269
/-- The exact ordered block digit is at most fifteen times the shell
cardinality: each threshold count is the cardinality of a filter. -/
theorem dyadicOrderedBlockDigit235_le_fifteen_mul_card (a : ℕ) :
    dyadicOrderedBlockDigit235 a ≤ 15 * (dyadicSmoothShell235 a).card := by
  have hthree := Finset.card_filter_le (dyadicSmoothShell235 a)
    (fun e => smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      3 ^ Nat.log 3 (2 ^ (a + 1)))
  have hfive := Finset.card_filter_le (dyadicSmoothShell235 a)
    (fun e => smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      5 ^ Nat.log 5 (2 ^ (a + 1)))
  unfold dyadicOrderedBlockDigit235 dyadicBeforeThresholdCount235
  split_ifs <;> omega
end ErdosProblems.Erdos269

open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution (a : ℕ) :
    dyadicOrderedBlockDigit235 a ≤ 15 * (a + 1) ^ 2 :=
  (dyadicOrderedBlockDigit235_le_fifteen_mul_card a).trans
    (Nat.mul_le_mul_left 15 (dyadicSmoothShell235_card_le_square a))
