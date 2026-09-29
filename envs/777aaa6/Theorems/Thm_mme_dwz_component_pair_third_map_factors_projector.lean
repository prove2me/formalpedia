-- Prove2me | Theorems.Thm_mme_dwz_component_pair_third_map_factors_projector
-- name    : mme_dwz_component_pair_third_map_factors_projector
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T01:13:25.801848+00:00
-- url     : https://prove2.me/theorems/a0a4054d-5871-40e5-85c3-d20a34ad7964
-- title:
--   Disallowed-word vanishing factors through the paired source projector
-- statement:
--   Fix a Table-2 row $s$ and scale $m$. Let $P$ be the canonical paired allowed-word projector and let $f$ be a linear map from the third mode of the unprojected pair to any $K$-vector space. Suppose $f(b_{w_1}\otimes b_{w_2})=0$ whenever either word has a split-count profile different from the prescribed one. Then
--   $$f\circ P_2=f.$$
--   Thus basis-word vanishing suffices for invariance under the literal source projector, for every Table-2 row and scale.
-- source:
--   Derived from the canonical paired allowed-word projector definitions and the accepted paired projection-inclusion tensor identity. This preserves the literal source of the Table-2 construction.

import Definitions.Def_mme_dwz_component_pair_projection_data
open MME MME.DWZComponentRestriction Module TensorProduct
universe u v
set_option autoImplicit false

theorem mme_dwz_component_pair_third_map_factors_projector
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ)
    {W : Type v} [AddCommGroup W] [Module K W]
    (f : (componentPairAmbient K s m).V 2 →ₗ[K] W)
    (hzero : ∀ w₁ w₂,
      (¬ componentWordAllowed s m w₁ ∨ ¬ componentWordAllowed s m w₂) →
      f (componentPowerZBasis K s m w₁ ⊗ₜ[K]
        componentPowerZBasis K s m w₂) = 0) :
    f.comp (componentPairProject K s m 2) = f := by sorry
