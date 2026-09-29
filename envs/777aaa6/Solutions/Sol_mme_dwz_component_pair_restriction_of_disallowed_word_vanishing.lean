-- Prove2me | solution 1 for mme_dwz_component_pair_restriction_of_disallowed_word_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T01:13:18.251874+00:00
-- url     : https://prove2.me/submissions/a87c5acc-1e89-4de1-990e-629b83cf5166

import Theorems.Thm_mme_dwz_component_pair_projection_inclusion_tensor
import Theorems.Thm_mme_dwz_component_pair_third_map_factors_projector

open MME MME.DWZComponentRestriction Module TensorProduct
universe u
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- A tensor map that kills the excluded Z-word pairs restricts from the
literal allowed-word source through its canonical inclusion. -/
theorem solution
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ) (T : TensorObj K 3)
    (maps : ∀ i, (componentPairAmbient K s m).V i →ₗ[K] T.V i)
    (htensor : PiTensorProduct.map maps (componentPairAmbient K s m).t = T.t)
    (hzero : ∀ w₁ w₂,
      (¬ componentWordAllowed s m w₁ ∨ ¬ componentWordAllowed s m w₂) →
      maps 2 (componentPowerZBasis K s m w₁ ⊗ₜ[K]
        componentPowerZBasis K s m w₂) = 0) :
    PiTensorProduct.map
        (fun i ↦ (maps i).comp (componentPairInclusion K s m i))
        (componentPairRestricted K s m).t = T.t := by
  have hfactor : ∀ i, (maps i).comp (componentPairProject K s m i) = maps i := by
    intro i
    fin_cases i
    · simp [componentPairProject, componentPowerProject, swapFirstTwoPerm,
        TensorProduct.map_id]
    · simp [componentPairProject, componentPowerProject, swapFirstTwoPerm,
        TensorProduct.map_id]
    · exact mme_dwz_component_pair_third_map_factors_projector s m (maps 2) hzero
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply,
    mme_dwz_component_pair_projection_inclusion_tensor,
    ← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  simpa only [hfactor] using htensor
