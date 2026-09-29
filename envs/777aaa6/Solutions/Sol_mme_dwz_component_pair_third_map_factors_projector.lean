-- Prove2me | solution 1 for mme_dwz_component_pair_third_map_factors_projector
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T01:13:34.551761+00:00
-- url     : https://prove2.me/submissions/8af9fbf3-bdba-4639-98f6-d09573d34d25

import Definitions.Def_mme_dwz_component_pair_projection_data

open MME MME.DWZComponentRestriction Module TensorProduct
universe u v
set_option autoImplicit false

/-- A map on the paired source descends through its canonical allowed-word
projector precisely when it kills the excluded basis pairs. -/
theorem solution
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ)
    {W : Type v} [AddCommGroup W] [Module K W]
    (f : (componentPairAmbient K s m).V 2 →ₗ[K] W)
    (hzero : ∀ w₁ w₂,
      (¬ componentWordAllowed s m w₁ ∨ ¬ componentWordAllowed s m w₂) →
      f (componentPowerZBasis K s m w₁ ⊗ₜ[K]
        componentPowerZBasis K s m w₂) = 0) :
    f.comp (componentPairProject K s m 2) = f := by
  classical
  apply ((componentPowerZBasis K s m).tensorProduct
    (componentPowerZBasis K s m)).ext
  rintro ⟨w₁, w₂⟩
  simp only [Basis.tensorProduct_apply]
  change f (TensorProduct.map (componentPowerProject K s m 2)
    (componentPowerProject K s m 2) (_ ⊗ₜ[K] _)) = _
  rw [TensorProduct.map_tmul]
  simp only [componentPowerProject, Function.update_self, Basis.constr_basis]
  by_cases h₁ : componentWordAllowed s m w₁
  · by_cases h₂ : componentWordAllowed s m w₂
    · simp only [if_pos h₁, if_pos h₂]
      rfl
    · simp only [if_pos h₁, if_neg h₂, TensorProduct.tmul_zero]
      exact f.map_zero.trans (hzero w₁ w₂ (Or.inr h₂)).symm
  · simp only [if_neg h₁, TensorProduct.zero_tmul]
    exact f.map_zero.trans (hzero w₁ w₂ (Or.inl h₁)).symm
