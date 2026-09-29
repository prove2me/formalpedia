-- Prove2me | solution 1 for Teichmuller.exists_min_teichDist_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T09:26:25.987365+00:00
-- url     : https://prove2.me/submissions/5b5ae269-d5e6-4e35-9a7b-44aca81c1fee

import Definitions.Def_Geometry_Teichmuller_TorusSpace
open Teichmuller Complex UpperHalfPlane Matrix MatrixGroups in
theorem solution (z w : ℍ) :
    ∃ g₀ : SL(2, ℤ), ∀ g : SL(2, ℤ), teichDist z (g₀ • w) ≤ teichDist z (g • w) := by
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
  have hfin : Set.Finite {γ : 𝒮ℒ | ((γ • ·) '' {w} ∩ Metric.closedBall z (dist z w)).Nonempty} :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image isCompact_singleton
      (isCompact_closedBall z (dist z w))
  let φ : SL(2, ℤ) → 𝒮ℒ := fun g => ⟨SpecialLinearGroup.mapGL ℝ g, g, rfl⟩
  have hφ : Function.Injective φ := by
    intro a b h
    exact SpecialLinearGroup.mapGL_injective (congrArg Subtype.val h)
  have hact : ∀ g : SL(2, ℤ), φ g • w = g • w := fun g => rfl
  have hS : Set.Finite {g : SL(2, ℤ) | dist z (g • w) ≤ dist z w} := by
    refine (hfin.preimage hφ.injOn).subset ?_
    intro g hg
    refine ⟨g • w, ⟨w, rfl, hact g⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_comm]
    exact hg
  obtain ⟨g₀, hg₀, hmin⟩ := Set.exists_min_image _ (fun g : SL(2, ℤ) => dist z (g • w)) hS
    ⟨1, by simp⟩
  refine ⟨g₀, fun g => ?_⟩
  rw [hhalf, hhalf]
  by_cases hg : dist z (g • w) ≤ dist z w
  · have := hmin g hg
    simp only at this
    linarith
  · push Not at hg
    have h0 : dist z (g₀ • w) ≤ dist z w := hg₀
    linarith
