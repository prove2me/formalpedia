-- Prove2me | solution 2 for Teichmuller.dil_affine
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T08:56:09.897962+00:00
-- url     : https://prove2.me/submissions/3e97c98f-c962-4107-bf12-f7403e1c9926

import Definitions.Def_Geometry_Teichmuller_TorusSpace
open Teichmuller Complex UpperHalfPlane in
theorem solution (τ τ' : ℍ) : (affine τ τ').dil
    = (‖(τ' : ℂ) - cbar τ‖ + ‖(τ' : ℂ) - (τ : ℂ)‖) ^ 2 / (4 * τ.im * τ'.im) := by
  have hy := τ.im_pos
  have hy' := τ'.im_pos
  have hpq : ‖(τ' : ℂ) - cbar τ‖ ^ 2 = ‖(τ' : ℂ) - (τ : ℂ)‖ ^ 2 + 4 * τ.im * τ'.im :=
    normSq_sub_cbar τ τ'
  have hlt : ‖(τ' : ℂ) - (τ : ℂ)‖ < ‖(τ' : ℂ) - cbar τ‖ := norm_sub_lt_norm_sub_cbar τ τ'
  have hdil : (affine τ τ').dil
      = (‖(τ' : ℂ) - cbar τ‖ + ‖(τ' : ℂ) - (τ : ℂ)‖) / (‖(τ' : ℂ) - cbar τ‖ - ‖(τ' : ℂ) - (τ : ℂ)‖) := by
    simp only [LinMap.dil, affine, norm_div, norm_sub_cbar_self]
    rw [norm_sub_rev (τ : ℂ) (τ' : ℂ)]
    have h2 : 0 < 2 * τ.im := by positivity
    rw [← add_div, ← sub_div, div_div_div_cancel_right₀ h2.ne']
  have hd : 0 < ‖(τ' : ℂ) - cbar τ‖ - ‖(τ' : ℂ) - (τ : ℂ)‖ := by linarith
  rw [hdil, div_eq_div_iff hd.ne' (by positivity)]
  linear_combination (-(‖(τ' : ℂ) - cbar τ‖ + ‖(τ' : ℂ) - (τ : ℂ)‖)) * hpq
