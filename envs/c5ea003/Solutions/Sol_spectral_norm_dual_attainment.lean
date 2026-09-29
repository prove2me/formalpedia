-- Prove2me | solution 1 for spectral_norm_dual_attainment
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T03:54:35.882177+00:00
-- url     : https://prove2.me/submissions/3cd7631c-c2bb-465a-8e6b-e5356897470f

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Order.Compact
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

-- Dual attainment of the spectral (operator) norm: there exist unit vectors x, y
-- attaining ⟪Xx, y⟫ = spectralNorm X.
theorem solution
    {n1 n2 : ℕ} (X : RealMatrix n1 n2) :
    ∃ (x : EuclideanSpace ℝ (Fin n2)) (y : EuclideanSpace ℝ (Fin n1)),
      ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
      ⟪Matrix.toEuclideanLin X x, y⟫_ℝ = spectralNorm X := by
  classical
  set A := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X) with hA
  -- maximize ‖A x‖ over the closed unit ball
  set f : EuclideanSpace ℝ (Fin n2) → ℝ := fun x => ‖A x‖ with hf
  have hcompact : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n2)) 1) :=
    isCompact_closedBall _ _
  have hne : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n2)) 1).Nonempty :=
    ⟨0, by simp⟩
  have hcont : ContinuousOn f (Metric.closedBall 0 1) :=
    (A.continuous.norm).continuousOn
  obtain ⟨x0, hx0mem, hx0max⟩ := hcompact.exists_isMaxOn hne hcont
  have hx0norm : ‖x0‖ ≤ 1 := by
    rwa [Metric.mem_closedBall, dist_zero_right] at hx0mem
  -- f x0 = spectralNorm X = ‖A‖
  have hmax : ∀ z, ‖z‖ ≤ 1 → ‖A z‖ ≤ f x0 := by
    intro z hz
    have : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n2)) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hz
    exact hx0max this
  -- upper: f x0 = ‖A x0‖ ≤ ‖A‖ * ‖x0‖ ≤ ‖A‖
  have hupper : f x0 ≤ spectralNorm X := by
    have : ‖A x0‖ ≤ ‖A‖ * ‖x0‖ := A.le_opNorm x0
    calc f x0 = ‖A x0‖ := rfl
      _ ≤ ‖A‖ * ‖x0‖ := this
      _ ≤ ‖A‖ * 1 := by
            apply mul_le_mul_of_nonneg_left hx0norm (norm_nonneg _)
      _ = spectralNorm X := by rw [mul_one, spectralNorm, ← hA]
  -- lower: ‖A‖ ≤ f x0 via opNorm_le_bound
  have hlower : spectralNorm X ≤ f x0 := by
    rw [spectralNorm, ← hA]
    apply A.opNorm_le_bound
    · exact norm_nonneg _  -- 0 ≤ f x0 = ‖A x0‖
    · intro z
      rcases eq_or_ne z 0 with hz | hz
      · subst hz; simp
      · have hznz : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
        have hunit : ‖(‖z‖⁻¹ : ℝ) • z‖ ≤ 1 := by
          rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hznz]
          rw [inv_mul_cancel₀ (ne_of_gt hznz)]
        have := hmax ((‖z‖⁻¹ : ℝ) • z) hunit
        rw [map_smul, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hznz] at this
        -- this : ‖z‖⁻¹ * ‖A z‖ ≤ f x0
        have h2 : ‖A z‖ ≤ f x0 * ‖z‖ := by
          have hmul := mul_le_mul_of_nonneg_right this (le_of_lt hznz)
          rw [mul_comm (‖z‖⁻¹) (‖A z‖), mul_assoc, inv_mul_cancel₀ (ne_of_gt hznz),
            mul_one] at hmul
          exact hmul
        exact h2
  have hfeq : f x0 = spectralNorm X := le_antisymm hupper hlower
  -- now build y
  rcases eq_or_ne (A x0) 0 with hAx0 | hAx0
  · refine ⟨x0, 0, hx0norm, by simp, ?_⟩
    show ⟪Matrix.toEuclideanLin X x0, (0:EuclideanSpace ℝ (Fin n1))⟫_ℝ = spectralNorm X
    rw [inner_zero_right]
    have : f x0 = ‖A x0‖ := rfl
    rw [hAx0] at this; simp at this
    rw [← hfeq, this]
  · refine ⟨x0, (‖A x0‖⁻¹ : ℝ) • A x0, hx0norm, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [inv_mul_cancel₀ (by positivity)]
    · show ⟪Matrix.toEuclideanLin X x0, (‖A x0‖⁻¹ : ℝ) • A x0⟫_ℝ = spectralNorm X
      have hAx0eq : Matrix.toEuclideanLin X x0 = A x0 := rfl
      rw [hAx0eq, inner_smul_right, real_inner_self_eq_norm_sq]
      rw [← hfeq]
      have : f x0 = ‖A x0‖ := rfl
      rw [this]
      field_simp
