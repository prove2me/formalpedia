-- Prove2me | solution 1 for dlp_conditional_lemma2_sigma_fiber_mixed3_chaos_inl
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-24T02:57:47.687453+00:00
-- url     : https://prove2.me/submissions/bcfbe007-1f90-44fc-a01d-1c0d9bd2380b

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_rademacher
import Theorems.Thm_rademacher_mixed3_chaos_l4_l2_bonami_hypercontractivity
import Theorems.Thm_rademacher_lower_tail_positivity_from_l4_l2_hypercontractivity
import Theorems.Thm_spectral_norm_dual_attainment
import Theorems.Thm_spectral_norm_inner_pairing_bound
import Mathlib.Analysis.InnerProductSpace.Basic
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

/-- de la Peña §4 eq(6) conditional Lemma 2 on the concrete matrix σ-sign MIXED
(linear + bilinear + trilinear, degree-≤3) chaos (fully-inlined statement, `_inl`).

The fluctuation `ξ_σ = 8·decoupled(Z_σ) − T_{n,3}` of dlP's order-3 forward bound carries
generically-nonzero LINEAR (r=1) and BILINEAR (r=2) terms in addition to the trilinear
(r=3) term; this is exactly dlP Lemma 2's degree-≤k tetrahedral chaos `Σ_{r=1}^k`. This
node is the order-3 mixed analog of `dlp_conditional_lemma2_sigma_fiber_mixed_chaos_inl`
(033da3b7), using the GENERAL degree-≤3 Bonami hypercontractivity
(`rademacher_mixed3_chaos_l4_l2_...`, K=729) in place of the degree-2 one.

Reference: de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4 Lemma 2 / Prop 1
(degree-≤k chaos `Σ_{r=1}^k`, /tmp/dlp.txt lines 199–235) + Kwapień–Szulga 1991 eq (1.4);
O'Donnell *Analysis of Boolean Functions* §9.1 (general Bonami). Constant 1/2916 = 1/(4·729). -/
theorem solution
    {n1 n2 : Nat}
    (b : (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (cc : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (T : RealMatrix n1 n2)
    (xv : EuclideanSpace ℝ (Fin n2)) (yv : EuclideanSpace ℝ (Fin n1))
    (hxv : ‖xv‖ ≤ 1) (hyv : ‖yv‖ ≤ 1)
    (hnorm : ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ = spectralNorm T)
    (hmean :
      rademacherExpectation
        (fun eps => ⟪Matrix.toEuclideanLin
          ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • b w)
            + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))
            + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                      * rademacherSign eps w3.1 w3.2) • cc w1 w2 w3))) xv, yv⟫_ℝ) = 0)
    (hvar :
      0 < rademacherExpectation
        (fun eps => (⟪Matrix.toEuclideanLin
          ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • b w)
            + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))
            + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                      * rademacherSign eps w3.1 w3.2) • cc w1 w2 w3))) xv, yv⟫_ℝ) ^ 2)) :
    rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T +
            ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • b w)
              + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
                (if w1 = w2 then (0 : RealMatrix n1 n2)
                 else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))
              + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
                (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
                 else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                        * rademacherSign eps w3.1 w3.2) • cc w1 w2 w3))))
          then (1 : ℝ) else 0) ≥ 1 / 2916 := by
  classical
  -- Rebind the inlined matrix MIXED degree-≤3 chaos.
  set Xi : Finset (Fin n1 × Fin n2) → RealMatrix n1 n2 :=
    fun eps =>
      (∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • b w)
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
          (if w1 = w2 then (0 : RealMatrix n1 n2)
           else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
           else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                  * rademacherSign eps w3.1 w3.2) • cc w1 w2 w3)) with hXi
  set F : Finset (Fin n1 × Fin n2) → ℝ :=
    fun eps => ⟪Matrix.toEuclideanLin (Xi eps) xv, yv⟫_ℝ with hF
  -- scalar dual coefficients (linear + bilinear + trilinear)
  set bc : (Fin n1 × Fin n2) → ℝ :=
    fun w => ⟪Matrix.toEuclideanLin (b w) xv, yv⟫_ℝ with hbc
  set ac : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ :=
    fun w1 w2 => ⟪Matrix.toEuclideanLin (a w1 w2) xv, yv⟫_ℝ with hac
  set ccc : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ :=
    fun w1 w2 w3 => ⟪Matrix.toEuclideanLin (cc w1 w2 w3) xv, yv⟫_ℝ with hccc
  have hFchaos :
      ∀ eps,
        F eps =
          (∑ w : Fin n1 × Fin n2, bc w * rademacherSign eps w.1 w.2)
            + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
                (if w1 = w2 then (0 : ℝ)
                 else ac w1 w2 * rademacherSign eps w1.1 w1.2
                              * rademacherSign eps w2.1 w2.2))
            + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
                (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : ℝ)
                 else ccc w1 w2 w3 * rademacherSign eps w1.1 w1.2
                              * rademacherSign eps w2.1 w2.2
                              * rademacherSign eps w3.1 w3.2)) := by
    intro eps
    simp only [hF, hXi]
    rw [map_add, LinearMap.add_apply, inner_add_left]
    rw [map_add, LinearMap.add_apply, inner_add_left]
    congr 1
    congr 1
    · -- linear half
      rw [map_sum, LinearMap.sum_apply, sum_inner]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [map_smul, LinearMap.smul_apply, inner_smul_left]
      simp only [hbc, conj_trivial]
      ring
    · -- bilinear half
      rw [map_sum, LinearMap.sum_apply, sum_inner]
      refine Finset.sum_congr rfl (fun w1 _ => ?_)
      rw [map_sum, LinearMap.sum_apply, sum_inner]
      refine Finset.sum_congr rfl (fun w2 _ => ?_)
      by_cases h : w1 = w2
      · simp [h]
      · simp only [if_neg h]
        rw [map_smul, LinearMap.smul_apply, inner_smul_left]
        simp only [hac, conj_trivial]
        ring
    · -- trilinear half
      rw [map_sum, LinearMap.sum_apply, sum_inner]
      refine Finset.sum_congr rfl (fun w1 _ => ?_)
      rw [map_sum, LinearMap.sum_apply, sum_inner]
      refine Finset.sum_congr rfl (fun w2 _ => ?_)
      rw [map_sum, LinearMap.sum_apply, sum_inner]
      refine Finset.sum_congr rfl (fun w3 _ => ?_)
      by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
      · simp [h]
      · simp only [if_neg h]
        rw [map_smul, LinearMap.smul_apply, inner_smul_left]
        simp only [hccc, conj_trivial]
        ring
  have hBonami :
      rademacherExpectation (fun eps => (F eps) ^ 4) ≤
        729 * (rademacherExpectation (fun eps => (F eps) ^ 2)) ^ 2 := by
    have hb := rademacher_mixed3_chaos_l4_l2_bonami_hypercontractivity (n₁ := n1) (n₂ := n2) bc ac ccc
    have hshape :
        F =
          (fun eps =>
            (∑ w : Fin n1 × Fin n2, bc w * rademacherSign eps w.1 w.2)
              + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
                (if w1 = w2 then (0 : ℝ)
                 else ac w1 w2 * rademacherSign eps w1.1 w1.2
                              * rademacherSign eps w2.1 w2.2))
              + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
                (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : ℝ)
                 else ccc w1 w2 w3 * rademacherSign eps w1.1 w1.2
                              * rademacherSign eps w2.1 w2.2
                              * rademacherSign eps w3.1 w3.2))) := by
      funext eps; exact hFchaos eps
    rw [hshape]
    exact hb
  have hmean' : rademacherExpectation F = 0 := by rw [hF]; exact hmean
  have hvar' : 0 < rademacherExpectation (fun eps => (F eps) ^ 2) := by rw [hF]; exact hvar
  have hpos :
      (1 : ℝ) / (4 * 729) ≤
        rademacherExpectation (fun eps => if 0 ≤ F eps then (1 : ℝ) else 0) :=
    rademacher_lower_tail_positivity_from_l4_l2_hypercontractivity
      (n₁ := n1) (n₂ := n2) 729 F (by norm_num) hmean' hvar' hBonami
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
  have hchase : (1 : ℝ) / 2916 ≤
      rademacherExpectation (fun eps => if 0 ≤ F eps then (1 : ℝ) else 0) := by
    have h2916 : (1 : ℝ) / (4 * 729) = 1 / 2916 := by norm_num
    rw [h2916] at hpos; exact hpos
  have hgoal :
      rademacherExpectation
          (fun eps =>
            if spectralNorm T ≤ spectralNorm (T + Xi eps)
            then (1 : ℝ) else 0) ≥ 1 / 2916 := by linarith [hmono, hchase]
  exact hgoal
