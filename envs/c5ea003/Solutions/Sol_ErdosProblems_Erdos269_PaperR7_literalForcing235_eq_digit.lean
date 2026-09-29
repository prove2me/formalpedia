-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.literalForcing235_eq_digit
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:16:46.251666+00:00
-- url     : https://prove2.me/submissions/ee9798a1-99ac-49c6-abf5-38cedb991ee8

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Erdos269_PaperR7ActualOrbit
import Theorems.Thm_ErdosProblems_Erdos269_half_threePrimeHeight_mul_dyadicShellMassQ235
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

/-!
# Round 7: literal forcing, infinite digit expansion and scaled dichotomy

Targets: short-note `res:dyadic-alphabet`, the dynamical clauses of
`res:actual-orbit`, and long-record `res:actual-orbit`.
The total smooth-series reindexing is supplied separately in
`PaperR7SeriesIdentification`; nothing here silently identifies a formal tsum
with the smooth-number series without that bridge.

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
    literalForcing235 a = (dyadicOrderedBlockDigit235 a : ℚ) := by
  rw [← half_threePrimeHeight_mul_dyadicShellMassQ235 a]
  unfold literalForcing235 dyadicShellMassQ235
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring
