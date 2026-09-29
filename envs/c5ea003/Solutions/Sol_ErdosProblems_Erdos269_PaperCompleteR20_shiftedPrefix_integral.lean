-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.shiftedPrefix_integral
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:53:36.734731+00:00
-- url     : https://prove2.me/submissions/ea49b3f8-b4c5-41ab-b340-708d2f4a6a5a

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
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight235_cast_pos
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_height_windowProduct
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



















theorem shiftHeight_dvd_of_le {m n : ℕ} (h : m ≤ n) : shiftHeight m ∣ shiftHeight n := by
  refine ⟨actualWindowProduct m (n - m), ?_⟩
  simpa only [Nat.add_sub_of_le h] using height_windowProduct m (n - m)
end ErdosProblems.Erdos269.PaperCompleteR20

open PaperR7
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution (t : ℕ) : ∃ z : ℤ, shiftedPrefix t = (z : ℝ) := by
  have hterm : ∀ k ∈ Finset.range t, ∃ z : ℤ,
      (shiftHeight t : ℝ) * ((dyadicOrderedBlockDigit235 k : ℝ) /
        (shiftHeight (k + 1) : ℝ)) = (z : ℝ) := by
    intro k hk
    obtain ⟨z, hz⟩ := shiftHeight_dvd_of_le (by have := Finset.mem_range.mp hk; omega : k + 1 ≤ t)
    refine ⟨(z : ℤ) * dyadicOrderedBlockDigit235 k, ?_⟩
    have hp : (shiftHeight (k + 1) : ℝ) ≠ 0 := (threePrimeHeight235_cast_pos _).ne'
    rw [hz]
    push_cast
    field_simp
  classical
  choose z hz using hterm
  refine ⟨∑ k ∈ (Finset.range t).attach, z k.val k.property, ?_⟩
  unfold shiftedPrefix
  rw [Finset.mul_sum, ← Finset.sum_attach]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  exact hz k.val k.property
