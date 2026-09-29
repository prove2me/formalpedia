-- Prove2me | Theorems.Thm_mme_dwz_q6_121_common_halving_ambient_component_source_maps
-- name    : mme_dwz_q6_121_common_halving_ambient_component_source_maps
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T01:19:50.808991+00:00
-- url     : https://prove2.me/theorems/08804257-6c13-4ef6-ad1b-0b4ecbf0a2bf
-- title:
--   Literal paired 121 ambient source maps preserve component word vanishing
-- statement:
--   Let a primary $q=6$ family of length $N=c_{13}m$ have a common balanced halving. The literal unprojected 121 pair admits tensor-preserving mode maps $F_i$ to the paired oriented coupled powers. For every retained entry $p$, if either third-mode word is disallowed by the prescribed split counts, then
--   $$P_{p,2}F_2(b(w_1)\otimes b(w_2))=0.$$
--   The source is the canonical component power paired with its first-two-mode swap. No paired-inducedness assumption is needed for this source-map compatibility result. It does not assert simultaneous diagonal extraction or an unconditional capacity bound.
-- source:
--   Derived from the accepted canonical 121 swap-to-211 basis transport and paired common-halving component source maps. The transport is lifted recursively to powers and composed with the canonical pair router.

import Definitions.Def_mme_dwz_component_pair_projection_data
import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
import Definitions.Def_mme_kron_pow_mode_word_basis
open MME MME.PairedOrientedPackaging MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_dwz_q6_121_common_halving_ambient_component_source_maps
    {K : Type u} [Field K] (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily (DWZTable2Counts.component 13 * m) L G A H)
    (halving : family.CommonBalancedXYHalving) :
    let N := DWZTable2Counts.component 13 * m
    let target := TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N)
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)
    ∃ maps : ∀ i, (componentPairAmbient K 13 m).V i →ₗ[K] target.V i,
      PiTensorProduct.map maps (componentPairAmbient K 13 m).t = target.t ∧
      ∀ w₁ w₂,
        (¬ componentWordAllowed 13 m w₁ ∨ ¬ componentWordAllowed 13 m w₂) →
        ∀ p : Fin A × Fin H,
          ((componentProj (K := K) family halving p 2).comp (maps 2))
            (componentPowerZBasis K 13 m w₁ ⊗ₜ[K]
              componentPowerZBasis K 13 m w₂) = 0 := by sorry
