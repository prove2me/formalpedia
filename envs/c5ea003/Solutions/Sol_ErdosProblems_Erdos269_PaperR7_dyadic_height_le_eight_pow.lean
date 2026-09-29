-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.dyadic_height_le_eight_pow
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:04:37.15809+00:00
-- url     : https://prove2.me/submissions/dc450559-7840-4acd-8186-3797233f67e1

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_eight_pow_eq_two_pow_cube
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight_le_cube
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Normed
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

namespace ErdosProblems.Erdos269.PaperR7
end ErdosProblems.Erdos269.PaperR7

/-!
# Round 7: the literal `8640 / 343` shell bound

Target: the bound in short-note `res:actual-orbit`.  The supplied bound `90`
does not prove this sharper displayed constant.  We retain the actual shell
mass, prove its `8^{-a}` estimate, and sum the resulting majorant exactly.
This is NOT a proof of the separate long-record `Q(n_a)` bound.

No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7
open scoped BigOperators
end ErdosProblems.Erdos269.PaperR7

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution (a : ℕ) :
    (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) ≤ (8 : ℝ) ^ a := by
  have hnat := threePrimeHeight_le_cube 2 3 5 (2 ^ a) (by positivity)
  rw [← eight_pow_eq_two_pow_cube] at hnat
  exact_mod_cast hnat
