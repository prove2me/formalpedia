-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.actual_weighted_strip_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:12:21.201+00:00
-- url     : https://prove2.me/submissions/a473957b-9c85-491b-84c7-d10323a01c44

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
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangle
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangleReal
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_StripDecomposition
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_WeightedShiftArithmetic
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_PhaseStripDecomposition
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_mem_literalTriangle_iff
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_actual_numerator_eq_logarithmic_triangle
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_weighted_phase_transport
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_nested_finite_strip_decomposition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Intervals
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
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The printed integer-floor weights and their exact crossing factors. -/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open scoped BigOperators









theorem triangleTheta_pos {p : ℕ} (hp : 1 < p) : 0 < triangleTheta p := by
  unfold triangleTheta
  exact one_div_pos.mpr (Real.logb_pos (by norm_num) (by exact_mod_cast hp))











private theorem phase_weight_factor {p : ℕ} (hp : 1 < p) (a : ℕ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (p : ℝ) ^ (⌊((a : ℝ) + 1) * triangleTheta p⌋₊ -
      ⌊((a : ℝ) + t) * triangleTheta p⌋₊) =
      (p : ℝ) ^ (phaseFloor p a 1 - phaseFloor p a t) := by
  have hθ := (triangleTheta_pos hp).le
  have hle : ⌊((a : ℝ) + t) * triangleTheta p⌋₊ ≤
      ⌊((a : ℝ) + 1) * triangleTheta p⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right (show (a : ℝ) + t ≤ a + 1 by linarith) hθ)
  rw [← zpow_natCast, Int.natCast_sub hle,
    Int.natCast_floor_eq_floor (mul_nonneg (by positivity) hθ),
    Int.natCast_floor_eq_floor (mul_nonneg (by positivity) hθ)]
  rfl

theorem literalLogWeight_eq_phaseOmega (a : ℕ) (v : ℕ × ℕ) :
    (literalLogWeight a v : ℝ) = phaseOmega a (Int.fract (triangleLogPoint v)) := by
  simp only [literalLogWeight, Nat.cast_mul, Nat.cast_pow]
  rw [phase_weight_factor (by decide : 1 < (3 : ℕ)) a _
      (Int.fract_nonneg _) (Int.fract_lt_one _).le,
    phase_weight_factor (by decide : 1 < (5 : ℕ)) a _
      (Int.fract_nonneg _) (Int.fract_lt_one _).le]
  rfl

theorem actual_numerator_eq_phase_triangle (a : ℕ) :
    (dyadicOrderedBlockDigit235 a : ℝ) =
      ∑ v ∈ literalTriangle a, phaseOmega a (Int.fract (triangleLogPoint v)) := by
  rw [actual_numerator_eq_logarithmic_triangle]
  push_cast
  exact Finset.sum_congr rfl (fun v _ => literalLogWeight_eq_phaseOmega a v)

theorem literalTriangle_monotone : Monotone literalTriangle := by
  intro a b hab v hv
  apply mem_literalTriangle_iff.mpr
  exact (mem_literalTriangle_iff.mp hv).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.add_le_add_right hab 1))
end ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
theorem solution (c : ℕ → ℤ) (σ r a : ℕ) :
    shiftedNumerator c σ r a / 15 =
      ∑ s ∈ Finset.range (σ + 1),
        ∑ v ∈ entryStrip (fun n => literalTriangle (a + n * r)) s,
          phaseOmega a (Int.fract (triangleLogPoint v)) *
            ∑ ν ∈ Finset.Icc s σ, (c ν : ℝ) *
              phaseChi a (Int.fract (triangleLogPoint v)) (ν * r) := by
  have hT : Monotone (fun n => literalTriangle (a + n * r)) := by
    intro n m hnm
    exact literalTriangle_monotone (Nat.add_le_add_left (Nat.mul_le_mul_right r hnm) a)
  have hterm : ∀ ν, (c ν : ℝ) * shiftGamma a (ν * r) *
      (dyadicOrderedBlockDigit235 (a + ν * r) : ℝ) =
      ∑ v ∈ literalTriangle (a + ν * r),
        phaseOmega a (Int.fract (triangleLogPoint v)) *
          ((c ν : ℝ) * phaseChi a (Int.fract (triangleLogPoint v)) (ν * r)) := by
    intro ν
    rw [actual_numerator_eq_phase_triangle, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    calc
      _ = (c ν : ℝ) * (shiftGamma a (ν * r) *
          phaseOmega (a + ν * r) (Int.fract (triangleLogPoint v))) := by ring
      _ = _ := by rw [weighted_phase_transport]; ring
  unfold shiftedNumerator
  rw [mul_div_cancel_left₀ _ (by norm_num : (15 : ℝ) ≠ 0)]
  simp_rw [hterm]
  rw [nested_finite_strip_decomposition _ hT]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
