-- Prove2me | solution 1 for dlp_sigma_survival_degenerate_variance_branch
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T20:47:14.334038+00:00
-- url     : https://prove2.me/submissions/46189056-b21e-44f7-941f-cd1aa8aa358a

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_rademacher
import Theorems.Thm_spectral_norm_inner_pairing_bound
import Mathlib.Analysis.InnerProductSpace.Basic
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

/-
de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4, the DEGENERATE-VARIANCE
branch of the conditional Lemma 2 (eq 6) survival bound, on the concrete matrix
σ-sign chaos.  Companion to the positive-variance node 877ca976
(`dlp_conditional_lemma2_sigma_fiber_matrix_chaos_inl`), which REQUIRES
`hvar : 0 < E_σ[image²]`.

When the σ-chaos scalar dual image `F eps = ⟪toEuclideanLin (Ξ eps) xv, yv⟫`
is identically `0` over the sign fiber (the degenerate case 877ca976 cannot reach),
the survival event holds for EVERY sign realization: by the norming identity
`⟪toEuclideanLin T xv, yv⟫ = spectralNorm T` and the pairing bound
`⟪toEuclideanLin (T+Ξ) xv, yv⟫ ≤ spectralNorm (T+Ξ)·‖xv‖·‖yv‖ ≤ spectralNorm (T+Ξ)`
(d3228e1d, with ‖xv‖,‖yv‖ ≤ 1), one gets
`spectralNorm T = ⟪toEuclideanLin T xv, yv⟫ = ⟪toEuclideanLin (T+Ξ) xv, yv⟫ ≤ spectralNorm (T+Ξ)`
since `⟪toEuclideanLin Ξ xv, yv⟫ = F eps = 0`.  So the survival indicator is `1`
on every fiber and `rademacherExpectation (survival-indicator) = 1 ≥ 1/324`.

This is dlP §4's "the pairing functional gives `x'(a+Y) = x'(a) + x'(Y) ≥ x'(a) = ‖a‖`"
argument (Lemma 1 lines 197–198), specialised to the degenerate σ-fiber.

Source: dlP–MS 1995, §4, eqs (6)–(7) + Lemma 1 dual-functional step (p.2 lines 197–198).
-/

theorem solution
    {n1 n2 : Nat}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (T : RealMatrix n1 n2)
    (xv : EuclideanSpace ℝ (Fin n2)) (yv : EuclideanSpace ℝ (Fin n1))
    (hxv : ‖xv‖ ≤ 1) (hyv : ‖yv‖ ≤ 1)
    (hnorm : ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ = spectralNorm T)
    -- degenerate-variance hypothesis: the σ-chaos dual image vanishes on every fiber
    (hdegen : ∀ eps : Finset (Fin n1 × Fin n2),
      ⟪Matrix.toEuclideanLin
        (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
          (if w1 = w2 then (0 : RealMatrix n1 n2)
           else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)) xv, yv⟫_ℝ = 0) :
    rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T +
            (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)))
          then (1 : ℝ) else 0) ≥ 1 / 324 := by
  classical
  -- The survival indicator is identically 1 over the sign fiber.
  have hsurv : ∀ eps : Finset (Fin n1 × Fin n2),
      (if spectralNorm T ≤ spectralNorm (T +
        (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
          (if w1 = w2 then (0 : RealMatrix n1 n2)
           else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)))
      then (1 : ℝ) else 0) = 1 := by
    intro eps
    set Xi : RealMatrix n1 n2 :=
      ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
        (if w1 = w2 then (0 : RealMatrix n1 n2)
         else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2) with hXi
    have hdeg := hdegen eps
    rw [← hXi] at hdeg
    -- pairing of (T+Ξ) with (xv,yv): split linearly
    have hsplit : ⟪Matrix.toEuclideanLin (T + Xi) xv, yv⟫_ℝ
        = ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ + ⟪Matrix.toEuclideanLin Xi xv, yv⟫_ℝ := by
      rw [map_add]
      simp only [LinearMap.add_apply, inner_add_left]
    -- the pairing equals spectralNorm T (norming) + 0 (degenerate)
    have hpair : ⟪Matrix.toEuclideanLin (T + Xi) xv, yv⟫_ℝ = spectralNorm T := by
      rw [hsplit, hnorm, hdeg, add_zero]
    -- pairing bound: ⟪(T+Ξ)xv, yv⟫ ≤ spectralNorm (T+Ξ)·‖xv‖·‖yv‖ ≤ spectralNorm (T+Ξ)
    have hbound := spectral_norm_inner_pairing_bound (T + Xi) xv yv
    have hsn_nonneg : 0 ≤ spectralNorm (T + Xi) := by
      unfold spectralNorm; positivity
    have hle : spectralNorm T ≤ spectralNorm (T + Xi) := by
      rw [← hpair]
      refine le_trans hbound ?_
      -- spectralNorm (T+Ξ)·‖xv‖·‖yv‖ ≤ spectralNorm (T+Ξ)
      calc spectralNorm (T + Xi) * ‖xv‖ * ‖yv‖
          ≤ spectralNorm (T + Xi) * 1 * 1 := by
            apply mul_le_mul
            · apply mul_le_mul_of_nonneg_left hxv hsn_nonneg
            · exact hyv
            · exact norm_nonneg _
            · positivity
        _ = spectralNorm (T + Xi) := by ring
    rw [if_pos hle]
  -- rademacherExpectation of the (≡1) survival indicator = ∑ weight·1 = 1 ≥ 1/324
  have hval : rademacherExpectation
      (fun eps =>
        if spectralNorm T ≤ spectralNorm (T +
          (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)))
        then (1 : ℝ) else 0) = 1 := by
    unfold rademacherExpectation rademacherObservationWeight
    have hterm : ∀ eps : Finset (Fin n1 × Fin n2),
        ((1:ℝ) / 2) ^ Fintype.card (Fin n1 × Fin n2) *
          (if spectralNorm T ≤ spectralNorm (T +
            (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)))
          then (1 : ℝ) else 0)
        = ((1:ℝ) / 2) ^ Fintype.card (Fin n1 × Fin n2) := by
      intro eps; rw [hsurv eps, mul_one]
    rw [Finset.sum_congr rfl (fun eps _ => hterm eps)]
    rw [Finset.sum_const, Finset.card_univ]
    rw [show (Fintype.card (Finset (Fin n1 × Fin n2)))
        = 2 ^ (Fintype.card (Fin n1 × Fin n2)) from by
      simp [Fintype.card_finset]]
    rw [nsmul_eq_mul, div_pow, one_pow, Nat.cast_pow]
    have h2 : ((2:ℝ) ^ Fintype.card (Fin n1 × Fin n2)) ≠ 0 := by positivity
    field_simp
    norm_num
  rw [hval]; norm_num

#print axioms solution
