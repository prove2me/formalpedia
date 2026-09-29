-- Prove2me | solution 2 for Teichmuller.exists_teichDist_T_lt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T08:24:08.814866+00:00
-- url     : https://prove2.me/submissions/4850f9f2-d11c-4338-9bb3-8055dc2e2703

import Definitions.Def_Geometry_Teichmuller_ModuliSpace
open Teichmuller Complex UpperHalfPlane in
theorem solution {ε : ℝ} (hε : 0 < ε) : ∃ σ : ℍ, teichDist σ (ModularGroup.T • σ) < ε := by
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
  have hs : 0 < Real.sinh ε := Real.sinh_pos_iff.mpr hε
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = 1 / Real.sinh ε := ⟨_, rfl⟩
  have hY : 0 < Y := by rw [hYdef]; positivity
  refine ⟨⟨(Y : ℂ) * Complex.I, by simpa using hY⟩, ?_⟩
  rw [hhalf, ← Real.sinh_lt_sinh, sinh_half_dist, modular_T_smul, vadd_im, coe_vadd,
    Complex.dist_eq]
  have h1 : ‖(Y : ℂ) * Complex.I - (((1 : ℝ) : ℂ) + (Y : ℂ) * Complex.I)‖ = 1 := by
    rw [show (Y : ℂ) * Complex.I - (((1 : ℝ) : ℂ) + (Y : ℂ) * Complex.I) = -1 by push_cast; ring]
    simp
  have h2 : ((Y : ℂ) * Complex.I).im = Y := by simp
  have h3 : 1 / (2 * Y) = Real.sinh ε / 2 := by rw [hYdef]; field_simp
  simp only [UpperHalfPlane.coe_mk, UpperHalfPlane.im] at *
  rw [h1, h2, Real.sqrt_mul_self hY.le, h3]
  linarith
