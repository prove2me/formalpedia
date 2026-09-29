-- Prove2me | solution 1 for dlp_conditional_lemma2_sigma_fiber_matrix_chaos_inl
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T17:07:15.708478+00:00
-- url     : https://prove2.me/submissions/c5bfecd4-b5c5-4f80-9e44-39c48efda8d6

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_rademacher
import Theorems.Thm_rademacher_bilinear_chaos_l4_l2_bonami_hypercontractivity
import Theorems.Thm_rademacher_lower_tail_positivity_from_l4_l2_hypercontractivity
import Theorems.Thm_spectral_norm_dual_attainment
import Theorems.Thm_spectral_norm_inner_pairing_bound
import Mathlib.Analysis.InnerProductSpace.Basic
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

/-- de la Peña §4 eq(6) conditional Lemma 2 on the concrete matrix σ-sign chaos
(fully-inlined statement, `_inl`). -/
theorem solution
    {n1 n2 : Nat}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (T : RealMatrix n1 n2)
    (xv : EuclideanSpace ℝ (Fin n2)) (yv : EuclideanSpace ℝ (Fin n1))
    (hxv : ‖xv‖ ≤ 1) (hyv : ‖yv‖ ≤ 1)
    (hnorm : ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ = spectralNorm T)
    (hmean :
      rademacherExpectation
        (fun eps => ⟪Matrix.toEuclideanLin
          (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)) xv, yv⟫_ℝ) = 0)
    (hvar :
      0 < rademacherExpectation
        (fun eps => (⟪Matrix.toEuclideanLin
          (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)) xv, yv⟫_ℝ) ^ 2)) :
    rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T +
            (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)))
          then (1 : ℝ) else 0) ≥ 1 / 324 := by
  classical
  -- Rebind the inlined matrix chaos to recover the abstraction.
  set Xi : Finset (Fin n1 × Fin n2) → RealMatrix n1 n2 :=
    fun eps =>
      ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
        (if w1 = w2 then (0 : RealMatrix n1 n2)
         else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2) with hXi
  set F : Finset (Fin n1 × Fin n2) → ℝ :=
    fun eps => ⟪Matrix.toEuclideanLin (Xi eps) xv, yv⟫_ℝ with hF
  set c : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ :=
    fun w1 w2 => ⟪Matrix.toEuclideanLin (a w1 w2) xv, yv⟫_ℝ with hc
  have hFchaos :
      ∀ eps,
        F eps =
          ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : ℝ)
             else c w1 w2 * rademacherSign eps w1.1 w1.2
                          * rademacherSign eps w2.1 w2.2) := by
    intro eps
    simp only [hF, hXi]
    rw [map_sum, LinearMap.sum_apply, sum_inner]
    refine Finset.sum_congr rfl (fun w1 _ => ?_)
    rw [map_sum, LinearMap.sum_apply, sum_inner]
    refine Finset.sum_congr rfl (fun w2 _ => ?_)
    by_cases h : w1 = w2
    · simp [h]
    · simp only [if_neg h]
      rw [map_smul, LinearMap.smul_apply, inner_smul_left]
      simp only [hc, conj_trivial]
      ring
  have hBonami :
      rademacherExpectation (fun eps => (F eps) ^ 4) ≤
        81 * (rademacherExpectation (fun eps => (F eps) ^ 2)) ^ 2 := by
    have hb := rademacher_bilinear_chaos_l4_l2_bonami_hypercontractivity (n₁ := n1) (n₂ := n2) c
    have hshape :
        F =
          (fun eps =>
            (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : ℝ)
               else c w1 w2 * rademacherSign eps w1.1 w1.2
                            * rademacherSign eps w2.1 w2.2))) := by
      funext eps; exact hFchaos eps
    rw [hshape]
    exact hb
  -- Translate the inlined hypotheses to the abstracted `F`.
  have hmean' : rademacherExpectation F = 0 := by rw [hF]; exact hmean
  have hvar' : 0 < rademacherExpectation (fun eps => (F eps) ^ 2) := by rw [hF]; exact hvar
  have hpos :
      (1 : ℝ) / (4 * 81) ≤
        rademacherExpectation (fun eps => if 0 ≤ F eps then (1 : ℝ) else 0) :=
    rademacher_lower_tail_positivity_from_l4_l2_hypercontractivity
      (n₁ := n1) (n₂ := n2) 81 F (by norm_num) hmean' hvar' hBonami
  have hcontain :
      ∀ eps,
        (if 0 ≤ F eps then (1 : ℝ) else 0) ≤
          (if spectralNorm T ≤ spectralNorm (T + Xi eps)
           then (1 : ℝ) else 0) := by
    intro eps
    by_cases hFe : 0 ≤ F eps
    · have hsurv : spectralNorm T ≤ spectralNorm (T + Xi eps) := by
        rw [← hnorm]
        have hsplit :
            ⟪Matrix.toEuclideanLin (T + Xi eps) xv, yv⟫_ℝ
              = ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ + F eps := by
          simp only [hF, map_add]
          rw [LinearMap.add_apply, inner_add_left]
        have hub :
            ⟪Matrix.toEuclideanLin (T + Xi eps) xv, yv⟫_ℝ
              ≤ spectralNorm (T + Xi eps) * ‖xv‖ * ‖yv‖ :=
          spectral_norm_inner_pairing_bound (T + Xi eps) xv yv
        have hle1 :
            ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ
              ≤ ⟪Matrix.toEuclideanLin (T + Xi eps) xv, yv⟫_ℝ := by
          rw [hsplit]; linarith [hFe]
        have hsp_nonneg : 0 ≤ spectralNorm (T + Xi eps) := by
          rw [spectralNorm]; exact norm_nonneg _
        calc ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ
            ≤ ⟪Matrix.toEuclideanLin (T + Xi eps) xv, yv⟫_ℝ := hle1
          _ ≤ spectralNorm (T + Xi eps) * ‖xv‖ * ‖yv‖ := hub
          _ ≤ spectralNorm (T + Xi eps) * 1 * 1 := by
                apply mul_le_mul
                · apply mul_le_mul_of_nonneg_left hxv hsp_nonneg
                · exact hyv
                · exact norm_nonneg _
                · positivity
          _ = spectralNorm (T + Xi eps) := by ring
      simp only [if_pos hFe, if_pos hsurv, le_refl]
    · rw [if_neg hFe]
      positivity
  have hmono :
      rademacherExpectation (fun eps => if 0 ≤ F eps then (1 : ℝ) else 0) ≤
        rademacherExpectation
          (fun eps =>
            if spectralNorm T ≤ spectralNorm (T + Xi eps)
            then (1 : ℝ) else 0) := by
    unfold rademacherExpectation
    apply Finset.sum_le_sum
    intro eps _
    apply mul_le_mul_of_nonneg_left (hcontain eps)
    unfold rademacherObservationWeight
    positivity
  have hchase : (1 : ℝ) / 324 ≤
      rademacherExpectation (fun eps => if 0 ≤ F eps then (1 : ℝ) else 0) := by
    have h324 : (1 : ℝ) / (4 * 81) = 1 / 324 := by norm_num
    rw [h324] at hpos; exact hpos
  -- the goal's chaos is `Xi eps` after the `set`; conclude by monotonicity.
  have hgoal :
      rademacherExpectation
          (fun eps =>
            if spectralNorm T ≤ spectralNorm (T + Xi eps)
            then (1 : ℝ) else 0) ≥ 1 / 324 := by linarith [hmono]
  exact hgoal
