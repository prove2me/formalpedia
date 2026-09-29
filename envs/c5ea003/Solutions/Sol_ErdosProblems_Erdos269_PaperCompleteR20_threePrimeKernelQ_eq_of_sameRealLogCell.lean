-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.threePrimeKernelQ_eq_of_sameRealLogCell
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:58:03.940641+00:00
-- url     : https://prove2.me/submissions/936b3898-7a7e-4d2a-ad88-612a2e614bc2

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR10_realThreePrimeHeight_eq
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
    {p q r i j k i' j' k' : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hcell : SameThreePrimeRealLogCell p q r
      (smooth3Val p q r i j k : ℝ) (smooth3Val p q r i' j' k' : ℝ)) :
    threePrimeKernelQ p q r i j k =
      threePrimeKernelQ p q r i' j' k' := by
  have hx : 1 ≤ smooth3Val p q r i j k := by
    unfold smooth3Val
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hy : 1 ≤ smooth3Val p q r i' j' k' := by
    unfold smooth3Val
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hxR : (1 : ℝ) ≤ (smooth3Val p q r i j k : ℕ) := by exact_mod_cast hx
  have hyR : (1 : ℝ) ≤ (smooth3Val p q r i' j' k' : ℕ) := by exact_mod_cast hy
  have hheight := realThreePrimeHeight_eq_of_sameLogCell hcell
  rw [realThreePrimeHeight_eq hp hq hr hxR,
    realThreePrimeHeight_eq hp hq hr hyR] at hheight
  simp only [Nat.floor_natCast] at hheight
  simp only [threePrimeKernelQ, hheight]
