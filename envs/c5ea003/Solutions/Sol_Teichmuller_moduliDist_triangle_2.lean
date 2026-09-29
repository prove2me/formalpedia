-- Prove2me | solution 2 for Teichmuller.moduliDist_triangle
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T09:08:06.276824+00:00
-- url     : https://prove2.me/submissions/25375142-d8ce-4b03-b008-16202d11b8f5

import Definitions.Def_Geometry_Teichmuller_ModuliSpace
open Teichmuller Complex UpperHalfPlane Matrix MatrixGroups in
theorem solution (τ τ' τ'' : ℍ) : moduliDist τ τ'' ≤ moduliDist τ τ' + moduliDist τ' τ'' := by
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
  have hcast : ∀ (g : SL(2, ℤ)) (z : ℍ),
      g • z = (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g : SL(2, ℝ)) • z := by
    intro g z
    apply UpperHalfPlane.ext
    rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
    simp
  have hiso : ∀ (g : SL(2, ℤ)) (z w : ℍ), dist (g • z) (g • w) = dist z w := by
    intro g z w
    rw [hcast g z, hcast g w]
    exact dist_smul _ _ _
  have hbdd : ∀ a b : ℍ, BddBelow (Set.range fun g : SL(2, ℤ) => teichDist a (g • b)) := by
    intro a b
    refine ⟨0, ?_⟩
    rintro _ ⟨g, rfl⟩
    show 0 ≤ teichDist a (g • b)
    rw [hhalf]
    positivity
  unfold moduliDist
  have key : ∀ g₁ g₂ : SL(2, ℤ), (⨅ g : SL(2, ℤ), teichDist τ (g • τ''))
      ≤ teichDist τ (g₁ • τ') + teichDist τ' (g₂ • τ'') := by
    intro g₁ g₂
    refine (ciInf_le (hbdd τ τ'') (g₁ * g₂)).trans ?_
    rw [hhalf, hhalf, hhalf, mul_smul, ← hiso g₁ τ' (g₂ • τ'')]
    linarith [dist_triangle τ (g₁ • τ') (g₁ • g₂ • τ'')]
  have step1 : ∀ g₁ : SL(2, ℤ), (⨅ g : SL(2, ℤ), teichDist τ (g • τ'')) - teichDist τ (g₁ • τ')
      ≤ ⨅ g : SL(2, ℤ), teichDist τ' (g • τ'') := by
    intro g₁
    apply le_ciInf
    intro g₂
    linarith [key g₁ g₂]
  have step2 : (⨅ g : SL(2, ℤ), teichDist τ (g • τ'')) - (⨅ g : SL(2, ℤ), teichDist τ' (g • τ''))
      ≤ ⨅ g : SL(2, ℤ), teichDist τ (g • τ') := by
    apply le_ciInf
    intro g₁
    linarith [step1 g₁]
  linarith
