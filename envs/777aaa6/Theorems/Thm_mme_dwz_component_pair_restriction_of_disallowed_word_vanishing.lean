-- Prove2me | Theorems.Thm_mme_dwz_component_pair_restriction_of_disallowed_word_vanishing
-- name    : mme_dwz_component_pair_restriction_of_disallowed_word_vanishing
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T01:13:05.294415+00:00
-- url     : https://prove2.me/theorems/062478a0-eb69-4b08-94eb-28410d7af538
-- title:
--   Tensor maps descend to the literal paired allowed-word source
-- statement:
--   Fix a Table-2 row $s$, a scale $m$, and an output tensor $T$. Suppose mode maps $F_i$ send the unprojected paired component tensor to $T$, and the third map kills every basis pair in which either word is disallowed. Let $I_i$ be the canonical inclusions of the paired allowed-word source. Then
--   $$\left(\bigotimes_i(F_i\circ I_i)\right)t_{\mathrm{restricted}}=t_T.$$
--   The same output tensor is therefore a restriction of the literal paired allowed-word source. This is a conditional descent criterion: it requires the stated tensor equation and excluded-word vanishing, and does not assert that suitable extraction maps always exist.
-- source:
--   Derived from the canonical paired allowed-word projector definitions and the accepted paired projection-inclusion tensor identity. This preserves the literal source of the Table-2 construction.

import Definitions.Def_mme_dwz_component_pair_projection_data
open MME MME.DWZComponentRestriction Module TensorProduct
universe u v
set_option autoImplicit false

theorem mme_dwz_component_pair_restriction_of_disallowed_word_vanishing
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ) (T : TensorObj K 3)
    (maps : ∀ i, (componentPairAmbient K s m).V i →ₗ[K] T.V i)
    (htensor : PiTensorProduct.map maps (componentPairAmbient K s m).t = T.t)
    (hzero : ∀ w₁ w₂,
      (¬ componentWordAllowed s m w₁ ∨ ¬ componentWordAllowed s m w₂) →
      maps 2 (componentPowerZBasis K s m w₁ ⊗ₜ[K]
        componentPowerZBasis K s m w₂) = 0) :
    PiTensorProduct.map
        (fun i ↦ (maps i).comp (componentPairInclusion K s m i))
        (componentPairRestricted K s m).t = T.t := by sorry
