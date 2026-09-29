-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.actual_cubic_no_crossing_strips
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:12:20.756914+00:00
-- url     : https://prove2.me/submissions/48bfb267-37cf-478c-984f-337afc6c29a8

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_cubic_difference_boundary_strips
import Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_weighted_phase_transport
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
theorem solution (a r : ℕ)
    (hcross : ∀ ν : ℕ, ν ≤ 3 → ∀ v ∈ literalTriangle (a + ν * r),
      phaseCarry 3 a (Int.fract (triangleLogPoint v)) (ν * r) = 0 ∧
      phaseCarry 5 a (Int.fract (triangleLogPoint v)) (ν * r) = 0) :
    shiftedNumerator cubicShiftCoefficient 3 r a / 15 =
      -(∑ v ∈ literalTriangle (a + r) \ literalTriangle a,
          phaseOmega a (Int.fract (triangleLogPoint v))) +
        2 * (∑ v ∈ literalTriangle (a + 2 * r) \ literalTriangle (a + r),
          phaseOmega a (Int.fract (triangleLogPoint v))) -
        (∑ v ∈ literalTriangle (a + 3 * r) \ literalTriangle (a + 2 * r),
          phaseOmega a (Int.fract (triangleLogPoint v))) := by
  have hT : Monotone (fun n => literalTriangle (a + n * r)) := by
    intro n m hnm
    exact literalTriangle_monotone (Nat.add_le_add_left (Nat.mul_le_mul_right r hnm) a)
  have hweight : ∀ ν : ℕ, ν ≤ 3 →
      shiftGamma a (ν * r) * (dyadicOrderedBlockDigit235 (a + ν * r) : ℝ) =
        ∑ v ∈ literalTriangle (a + ν * r),
          phaseOmega a (Int.fract (triangleLogPoint v)) := by
    intro ν hν
    rw [actual_numerator_eq_phase_triangle, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    rw [weighted_phase_transport]
    have hc := hcross ν hν v hv
    simp only [phaseChi, hc.1, hc.2, neg_zero, zpow_zero, mul_one, one_mul]
  have hexpand : shiftedNumerator cubicShiftCoefficient 3 r a / 15 =
      (∑ v ∈ literalTriangle a, phaseOmega a (Int.fract (triangleLogPoint v))) -
        3 * (∑ v ∈ literalTriangle (a + r),
          phaseOmega a (Int.fract (triangleLogPoint v))) +
        3 * (∑ v ∈ literalTriangle (a + 2 * r),
          phaseOmega a (Int.fract (triangleLogPoint v))) -
        (∑ v ∈ literalTriangle (a + 3 * r),
          phaseOmega a (Int.fract (triangleLogPoint v))) := by
    unfold shiftedNumerator
    rw [mul_div_cancel_left₀ _ (by norm_num : (15 : ℝ) ≠ 0)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      mul_assoc, hweight 0 (by decide), hweight 1 (by decide),
      hweight 2 (by decide), hweight 3 (by decide)]
    norm_num [cubicShiftCoefficient]
    <;> ring
  rw [hexpand]
  simpa only [zero_mul, one_mul, add_zero] using
    cubic_difference_boundary_strips (fun n => literalTriangle (a + n * r)) hT
      (fun v => phaseOmega a (Int.fract (triangleLogPoint v)))
