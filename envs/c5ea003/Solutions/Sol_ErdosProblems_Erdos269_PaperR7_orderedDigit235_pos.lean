-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.orderedDigit235_pos
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:19:07.086339+00:00
-- url     : https://prove2.me/submissions/5c27e4a3-b180-4d71-84e1-d3f5457fd7b2

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
import Theorems.Thm_ErdosProblems_Erdos269_dyadicShellMassR235_pos
import Theorems.Thm_ErdosProblems_Erdos269_half_threePrimeHeight_mul_dyadicShellMassR235
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight235_cast_pos
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
theorem solution (a : ℕ) : 0 < dyadicOrderedBlockDigit235 a := by
  have hp : (0 : ℝ) <
      (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) / 2 * dyadicShellMassR235 a :=
    mul_pos (div_pos (threePrimeHeight235_cast_pos _) (by norm_num))
      (dyadicShellMassR235_pos a)
  rw [half_threePrimeHeight_mul_dyadicShellMassR235 a] at hp
  exact_mod_cast hp
