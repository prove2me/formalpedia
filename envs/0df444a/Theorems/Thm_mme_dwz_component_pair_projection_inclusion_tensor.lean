-- Prove2me | Theorems.Thm_mme_dwz_component_pair_projection_inclusion_tensor
-- name    : mme_dwz_component_pair_projection_inclusion_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T10:46:59.369349+00:00
-- url     : https://prove2.me/theorems/e6f1edd6-842a-4a15-acd2-8fb3b7fea881
-- title:
--   The paired Table-2 inclusion equals the paired allowed-word projector
-- statement:
--   For any Table-2 component row and scale, consider the literal pair consisting of the allowed-word projected component power and its copy with the first two tensor modes swapped. The tensor product of the two canonical inclusions maps this literal restricted pair to the same tensor as the tensor product projector $P\otimes P^{\mathrm{swap}}$ maps the unprojected ambient pair.
--
--   This is the exact source equation needed to descend a tensor-restriction or finite extraction certificate from the full paired component to its faithful allowed-word source. It changes no dimensions and makes no claim that the projected source contains the whole ambient tensor.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.4 and the paired 121/211 analysis in Section 7; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_component_pair_projection_data
import Theorems.Thm_mme_basisZAllowed_blockSubtensor_inclusion_tensor
import Definitions.Def_mme_TypeGrading_kron

open MME Module TensorProduct PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_component_pair_projection_inclusion_tensor
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ) :
    PiTensorProduct.map (componentPairInclusion K s m)
        (componentPairRestricted K s m).t =
      PiTensorProduct.map (componentPairProject K s m)
        (componentPairAmbient K s m).t := by
  sorry
