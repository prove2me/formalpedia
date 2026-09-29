-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.shiftedNumerator_integral
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:52:54.498207+00:00
-- url     : https://prove2.me/submissions/34017363-cacf-4135-a98b-533a4399e40c

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Erdos269_JumpConstraintMajorant
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
import Definitions.Def_ErdosProblems_Erdos269_PaperR7ActualOrbit
import Definitions.Def_ErdosProblems_Erdos269_PaperR7SeriesIdentification
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
import Definitions.Def_ErdosProblems_Erdos269_RationalityCarryBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7RationalBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7WindowResults
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_WeightedShiftArithmetic
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_shiftGamma_four_values
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
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
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace PaperR7
end PaperR7

/-!
# Exact arithmetic of the paper's weighted shifts

The ratio is defined from the actual dyadic heights. Integer logarithms
prove its four-element alphabet without numerical logarithms. The factor
15 clears both the shifted coefficients and the finite prefix correction.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open PaperR7
open scoped BigOperators













theorem fifteen_shiftGamma_integral (a t : ℕ) :
    ∃ z : ℤ, 15 * shiftGamma a t = (z : ℝ) := by
  rcases shiftGamma_four_values a t with h | h | h | h
  · exact ⟨15, by rw [h]; norm_num⟩
  · exact ⟨5, by rw [h]; norm_num⟩
  · exact ⟨3, by rw [h]; norm_num⟩
  · exact ⟨1, by rw [h]; norm_num⟩
end ErdosProblems.Erdos269.PaperCompleteR20

open PaperR7
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution (c : ℕ → ℤ) (σ r a : ℕ) :
    ∃ z : ℤ, shiftedNumerator c σ r a = (z : ℝ) := by
  choose z hz using fifteen_shiftGamma_integral a
  refine ⟨∑ j ∈ Finset.range (σ + 1), c j * z (j * r) *
    (dyadicOrderedBlockDigit235 (a + j * r) : ℤ), ?_⟩
  unfold shiftedNumerator
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hz (j * r)]
  ring
