-- Prove2me | solution 1 for ErdosProblems.Erdos269.dyadicShellTsumTailR235_eq_shell_add
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:42:38.018111+00:00
-- url     : https://prove2.me/submissions/f05ba4ce-fbd6-4a8f-8077-9921a94cce3c

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Theorems.Thm_ErdosProblems_Erdos269_summable_dyadicShellMassR235
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

open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution (a : ℕ) :
    dyadicShellTsumTailR235 a =
      dyadicShellMassR235 a + dyadicShellTsumTailR235 (a + 1) := by
  have ha : Summable (fun n : ℕ => dyadicShellMassR235 (a + n)) :=
    summable_dyadicShellMassR235.comp_injective fun _ _ h =>
      Nat.add_left_cancel h
  have hsplit := ha.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at hsplit
  unfold dyadicShellTsumTailR235
  simpa only [Nat.add_zero, Nat.add_assoc, Nat.one_add] using hsplit.symm
