-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.scaled_actual_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:12:46.846253+00:00
-- url     : https://prove2.me/submissions/93d59557-4e6f-45aa-b7bc-52cb914b7c44

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
import Theorems.Thm_ErdosProblems_Erdos269_dyadicNormalizedShellTsumTailR235_succ
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
theorem solution (B : ℤ) (a : ℕ) :
    (B : ℝ) * trueNormalizedState (a + 1) =
      (dyadicBlockBase235 a : ℝ) * ((B : ℝ) * trueNormalizedState a) -
        ((B * (dyadicOrderedBlockDigit235 a : ℤ) : ℤ) : ℝ) := by
  have h := dyadicNormalizedShellTsumTailR235_succ a
  change trueNormalizedState (a + 1) =
    (dyadicBlockBase235 a : ℝ) * trueNormalizedState a -
      (dyadicOrderedBlockDigit235 a : ℝ) at h
  rw [h]
  push_cast
  ring
