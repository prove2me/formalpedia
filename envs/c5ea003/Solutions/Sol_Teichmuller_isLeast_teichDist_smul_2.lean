-- Prove2me | solution 2 for Teichmuller.isLeast_teichDist_smul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T08:46:03.819257+00:00
-- url     : https://prove2.me/submissions/7fb45598-a97a-4a8d-a5bc-ca0c4cee605d

import Definitions.Def_Geometry_Teichmuller_TranslationLength
open Teichmuller Complex UpperHalfPlane Matrix MatrixGroups in
theorem solution {R : Type*} [CommRing R] [Algebra R ℝ] {g : SL(2, R)} (ht : 2 < |tr g|) :
    IsLeast {r : ℝ | ∃ τ : ℍ, r = teichDist τ (g • τ)} (Real.log (stretch g)) := by
  have hdet : entry g 0 0 * entry g 1 1 - entry g 0 1 * entry g 1 0 = 1 := by
    have h := congrArg (algebraMap R ℝ) g.det_coe
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, map_one] at h
    simpa [entry] using h
  have hcoe : ∀ z : ℍ, ((g • z : ℍ) : ℂ) = ((entry g 0 0 : ℂ) * z + (entry g 0 1 : ℂ)) /
      ((entry g 1 0 : ℂ) * z + (entry g 1 1 : ℂ)) := by
    intro z; rw [coe_specialLinearGroup_apply]; rfl
  have hnD : ∀ z : ℍ, 0 < (entry g 1 0 * z.re + entry g 1 1) ^ 2 + (entry g 1 0 * z.im) ^ 2 := by
    intro z
    have hy := z.im_pos
    by_contra hle
    push Not at hle
    have h1 : entry g 1 0 * z.im = 0 := by nlinarith [sq_nonneg (entry g 1 0 * z.re + entry g 1 1), sq_nonneg (entry g 1 0 * z.im)]
    have h2 : entry g 1 0 * z.re + entry g 1 1 = 0 := by nlinarith [sq_nonneg (entry g 1 0 * z.re + entry g 1 1), sq_nonneg (entry g 1 0 * z.im)]
    have hc : entry g 1 0 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · linarith
    rw [hc, zero_mul, zero_add] at h2
    rw [hc, h2] at hdet
    simp at hdet
  have hre : ∀ z : ℍ, (g • z).re = ((entry g 0 0 * z.re + entry g 0 1) * (entry g 1 0 * z.re + entry g 1 1)
      + entry g 0 0 * entry g 1 0 * z.im ^ 2) / ((entry g 1 0 * z.re + entry g 1 1) ^ 2 + (entry g 1 0 * z.im) ^ 2) := by
    intro z
    have := hnD z
    show ((g • z : ℍ) : ℂ).re = _
    rw [hcoe, Complex.div_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    field_simp
    ring
  have him : ∀ z : ℍ, (g • z).im = z.im / ((entry g 1 0 * z.re + entry g 1 1) ^ 2 + (entry g 1 0 * z.im) ^ 2) := by
    intro z
    have := hnD z
    show ((g • z : ℍ) : ℂ).im = _
    rw [hcoe, Complex.div_im, Complex.normSq_apply, ← sub_div]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    congr 1
    · linear_combination z.im * hdet
    · ring
  have hcd : ∀ z : ℍ, Real.cosh (dist z (g • z)) = (tr g ^ 2 - 2) / 2 +
      (entry g 1 0 * (z.re ^ 2 + z.im ^ 2) - (entry g 0 0 - entry g 1 1) * z.re - entry g 0 1) ^ 2
        / (2 * z.im ^ 2) := by
    intro z
    have hy := z.im_pos
    have hD := hnD z
    have key : ∀ a b c d x y : ℝ, 0 < y → 0 < (c * x + d) ^ 2 + (c * y) ^ 2 → a * d - b * c ≠ 0 →
        ((x - ((a * x + b) * (c * x + d) + a * c * y ^ 2) / ((c * x + d) ^ 2 + (c * y) ^ 2)) ^ 2 + y ^ 2
          + ((a * d - b * c) * y / ((c * x + d) ^ 2 + (c * y) ^ 2)) ^ 2)
          / (2 * y * ((a * d - b * c) * y / ((c * x + d) ^ 2 + (c * y) ^ 2)))
        = 1 + ((c * (x ^ 2 + y ^ 2) - (a - d) * x - b) ^ 2 + y ^ 2 * ((a + d) ^ 2 - 4 * (a * d - b * c)))
          / (2 * (a * d - b * c) * y ^ 2) := by
      intro a b c d x y hy hD hdet
      have hpoly : (x * ((c * x + d) ^ 2 + (c * y) ^ 2) - ((a * x + b) * (c * x + d) + a * c * y ^ 2)) ^ 2
          + y ^ 2 * ((c * x + d) ^ 2 + (c * y) ^ 2) ^ 2 + (a * d - b * c) ^ 2 * y ^ 2
        = ((c * x + d) ^ 2 + (c * y) ^ 2) * (2 * (a * d - b * c) * y ^ 2
          + (c * (x ^ 2 + y ^ 2) - (a - d) * x - b) ^ 2 + y ^ 2 * ((a + d) ^ 2 - 4 * (a * d - b * c))) := by
        ring
      generalize (c * x + d) ^ 2 + (c * y) ^ 2 = n at hD hpoly ⊢
      generalize a * d - b * c = δ at hdet hpoly ⊢
      generalize (a * x + b) * (c * x + d) + a * c * y ^ 2 = P at hpoly ⊢
      generalize c * (x ^ 2 + y ^ 2) - (a - d) * x - b = Q at hpoly ⊢
      have hn := hD.ne'
      have hy' := hy.ne'
      field_simp
      linear_combination hpoly
    have hk := key (entry g 0 0) (entry g 0 1) (entry g 1 0) (entry g 1 1) z.re z.im hy hD
      (by rw [hdet]; norm_num)
    rw [hdet] at hk
    rw [cosh_dist', hre, him]
    simp only [one_mul] at hk
    rw [hk]
    simp only [tr]
    field_simp
    ring
  have hexp : ∀ τ τ' : ℍ, (affine τ τ').dil = Real.exp (dist τ τ') := by
    intro τ τ'
    have hy := τ.im_pos
    have hy' := τ'.im_pos
    have hpq : ‖(τ' : ℂ) - cbar τ‖ ^ 2 = ‖(τ' : ℂ) - (τ : ℂ)‖ ^ 2 + 4 * τ.im * τ'.im :=
      normSq_sub_cbar τ τ'
    have hlt : ‖(τ' : ℂ) - (τ : ℂ)‖ < ‖(τ' : ℂ) - cbar τ‖ := norm_sub_lt_norm_sub_cbar τ τ'
    have hq0 : 0 ≤ ‖(τ' : ℂ) - (τ : ℂ)‖ := norm_nonneg _
    have hdil : (affine τ τ').dil
        = (‖(τ' : ℂ) - cbar τ‖ + ‖(τ' : ℂ) - (τ : ℂ)‖) / (‖(τ' : ℂ) - cbar τ‖ - ‖(τ' : ℂ) - (τ : ℂ)‖) := by
      simp only [LinMap.dil, affine, norm_div, norm_sub_cbar_self]
      rw [norm_sub_rev (τ : ℂ) (τ' : ℂ)]
      have h2 : 0 < 2 * τ.im := by positivity
      rw [← add_div, ← sub_div, div_div_div_cancel_right₀ h2.ne']
    have hconj : ‖(τ : ℂ) - (starRingEnd ℂ) (τ' : ℂ)‖ = ‖(τ' : ℂ) - cbar τ‖ := by
      rw [← Complex.norm_conj, map_sub, Complex.conj_conj, norm_sub_rev]
    have he : Real.exp (dist τ τ') = Real.exp (dist τ τ' / 2) ^ 2 := by
      rw [sq, ← Real.exp_add, add_halves]
    have hs : √(τ.im * τ'.im) ^ 2 = τ.im * τ'.im := Real.sq_sqrt (by positivity)
    have hs0 : 0 < √(τ.im * τ'.im) := Real.sqrt_pos.mpr (by positivity)
    have hd : 0 < ‖(τ' : ℂ) - cbar τ‖ - ‖(τ' : ℂ) - (τ : ℂ)‖ := by linarith
    rw [hdil, he, exp_half_dist, Complex.dist_eq, Complex.dist_eq, norm_sub_rev (τ : ℂ) (τ' : ℂ), hconj]
    rw [div_pow, mul_pow, hs, div_eq_div_iff hd.ne' (by positivity)]
    linear_combination (-(‖(τ' : ℂ) - cbar τ‖ + ‖(τ' : ℂ) - (τ : ℂ)‖)) * hpq
  have hhalf : ∀ τ τ' : ℍ, teichDist τ τ' = dist τ τ' / 2 := by
    intro τ τ'
    unfold teichDist
    rw [hexp, Real.log_exp]
  have ht2 : 4 < tr g ^ 2 := by nlinarith [sq_abs (tr g), abs_nonneg (tr g)]
  have hr : Real.sqrt (tr g ^ 2 - 4) ^ 2 = tr g ^ 2 - 4 := Real.sq_sqrt (by linarith)
  have hr0 : 0 ≤ Real.sqrt (tr g ^ 2 - 4) := Real.sqrt_nonneg _
  have hs1 : 1 < stretch g := by unfold stretch; linarith
  have hs0 : 0 < stretch g := by linarith
  have hsinv : stretch g * ((|tr g| - Real.sqrt (tr g ^ 2 - 4)) / 2) = 1 := by
    unfold stretch
    linear_combination (sq_abs (tr g)) / 4 - hr / 4
  have hcosh : Real.cosh (2 * Real.log (stretch g)) = (tr g ^ 2 - 2) / 2 := by
    have hinv : (stretch g)⁻¹ = (|tr g| - Real.sqrt (tr g ^ 2 - 4)) / 2 :=
      inv_eq_of_mul_eq_one_right hsinv
    rw [Real.cosh_eq, show 2 * Real.log (stretch g) = Real.log (stretch g) + Real.log (stretch g) by ring,
      neg_add, Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hs0, hinv]
    unfold stretch
    linear_combination (sq_abs (tr g)) / 4 + hr / 4
  have hE : ∀ a b c d r : ℝ, c ≠ 0 → r ^ 2 = (a + d) ^ 2 - 4 →
      c * (((a - d) / (2 * c)) ^ 2 + (r / (2 * |c|)) ^ 2) - (a - d) * ((a - d) / (2 * c)) - b
        = (a * d - b * c - 1) / c := by
    intro a b c d r hc hr
    rw [div_pow r, mul_pow, sq_abs, hr]
    field_simp
    ring
  obtain ⟨z0, hz0⟩ : ∃ z : ℍ,
      entry g 1 0 * (z.re ^ 2 + z.im ^ 2) - (entry g 0 0 - entry g 1 1) * z.re - entry g 0 1 = 0 := by
    by_cases hc : entry g 1 0 = 0
    · have had : entry g 0 0 * entry g 1 1 = 1 := by rw [hc, mul_zero, sub_zero] at hdet; exact hdet
      have hne : entry g 0 0 - entry g 1 1 ≠ 0 := by
        intro h0
        have h4 : tr g ^ 2 = 4 := by
          simp only [tr]
          linear_combination (entry g 0 0 - entry g 1 1) * h0 + 4 * had
        linarith
      refine ⟨UpperHalfPlane.mk (((-entry g 0 1 / (entry g 0 0 - entry g 1 1) : ℝ) : ℂ) + Complex.I)
        (by simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]; norm_num), ?_⟩
      simp only [UpperHalfPlane.re, UpperHalfPlane.im, UpperHalfPlane.coe_mk, hc]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, add_zero, zero_add, zero_mul]
      field_simp
      ring
    · refine ⟨UpperHalfPlane.mk ((((entry g 0 0 - entry g 1 1) / (2 * entry g 1 0) : ℝ) : ℂ)
        + ((Real.sqrt (tr g ^ 2 - 4) / (2 * |entry g 1 0|) : ℝ) : ℂ) * Complex.I) (by
          have : 0 < Real.sqrt (tr g ^ 2 - 4) := Real.sqrt_pos.mpr (by linarith)
          simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
            Complex.I_re, Complex.I_im, mul_zero, zero_add, mul_one]
          positivity), ?_⟩
      simp only [UpperHalfPlane.re, UpperHalfPlane.im, UpperHalfPlane.coe_mk]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
        Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
      rw [hE _ _ _ _ _ hc (by rw [hr]; simp only [tr]), hdet, sub_self, zero_div]
  have hlog0 : 0 ≤ 2 * Real.log (stretch g) := by have := Real.log_pos hs1; linarith
  refine ⟨⟨z0, ?_⟩, ?_⟩
  · rw [hhalf]
    have h1 : Real.cosh (dist z0 (g • z0)) = Real.cosh (2 * Real.log (stretch g)) := by
      rw [hcd, hz0, hcosh]; simp
    have e1 := Real.cosh_le_cosh.mp h1.le
    have e2 := Real.cosh_le_cosh.mp h1.ge
    rw [abs_of_nonneg dist_nonneg, abs_of_nonneg hlog0] at e1 e2
    linarith
  · rintro r ⟨τ, rfl⟩
    rw [hhalf]
    have h1 : Real.cosh (2 * Real.log (stretch g)) ≤ Real.cosh (dist τ (g • τ)) := by
      rw [hcd, hcosh]
      have := τ.im_pos
      have : 0 ≤ (entry g 1 0 * (τ.re ^ 2 + τ.im ^ 2) - (entry g 0 0 - entry g 1 1) * τ.re
        - entry g 0 1) ^ 2 / (2 * τ.im ^ 2) := by positivity
      linarith
    have e := Real.cosh_le_cosh.mp h1
    rw [abs_of_nonneg dist_nonneg, abs_of_nonneg hlog0] at e
    linarith
