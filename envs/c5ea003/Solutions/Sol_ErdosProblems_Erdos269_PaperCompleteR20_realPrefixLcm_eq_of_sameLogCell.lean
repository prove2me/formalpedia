-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_eq_of_sameLogCell
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:29:25.481339+00:00
-- url     : https://prove2.me/submissions/8ff47fe6-8f9a-497c-8e7a-d0610276ee27

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
import Definitions.Def_ErdosProblems_Erdos269_RealCutoffR10
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_RealCutoffs
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_running_lcm_real_cutoff_exact
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Real.Archimedean
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PaperR10
end PaperR10

/-!
# Literal real cutoffs for the Erdős 269 paper

The paper quantifies its prefix cutoffs and shell endpoints over the reals.
This module transports the existing natural-cutoff arithmetic through
`Nat.floor` and proves the short-shell injection directly for real endpoints.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open Finset
open scoped BigOperators

noncomputable section

open PaperR10









/-- The height is constant on a literal real logarithmic cell. -/
theorem realThreePrimeHeight_eq_of_sameLogCell
    {p q r : ℕ} {x y : ℝ}
    (hcell : SameThreePrimeRealLogCell p q r x y) :
    realThreePrimeHeight p q r x = realThreePrimeHeight p q r y := by
  rcases hcell with ⟨hp, hq, hr⟩
  simp [realThreePrimeHeight, hp, hq, hr]
end
end ErdosProblems.Erdos269.PaperCompleteR20

open Finset
open scoped BigOperators
open PaperR10
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
open ErdosProblems.Erdos269.PaperR10 in
theorem solution
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hcell : SameThreePrimeRealLogCell p q r x y) :
    realPrefixLcm p q r x = realPrefixLcm p q r y := by
  rw [running_lcm_real_cutoff_exact hp hq hr hpq hpr hqr hx,
    running_lcm_real_cutoff_exact hp hq hr hpq hpr hqr hy]
  exact realThreePrimeHeight_eq_of_sameLogCell hcell
