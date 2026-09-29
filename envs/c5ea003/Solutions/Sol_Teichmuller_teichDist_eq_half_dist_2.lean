-- Prove2me | solution 2 for Teichmuller.teichDist_eq_half_dist
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T08:51:34.421746+00:00
-- url     : https://prove2.me/submissions/c1d35687-d406-4cc8-a2a4-707986ff5a33

import Definitions.Def_Geometry_Teichmuller_TorusSpace
open Teichmuller Complex UpperHalfPlane in
theorem solution (τ τ' : ℍ) : teichDist τ τ' = dist τ τ' / 2 := by
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
  unfold teichDist
  rw [hexp, Real.log_exp]
