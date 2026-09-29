-- Prove2me | Theorems.Thm_mme_dwz_source_broken_restrict_of_grouped_basis_router
-- name    : mme_dwz_source_broken_restrict_of_grouped_basis_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T17:22:11.74659+00:00
-- url     : https://prove2.me/theorems/140d3200-5395-4139-8af5-33d7c3cc4b62
-- title:
--   Source broken Table-2 owners descend through a grouped basis router
-- statement:
--   Fix one retained Table-2 outer word, its source-order broken copy, and a transported broken copy of the grouped standard block. Suppose a full-tensor regrouping sends the source coarse-address tensor to a target tensor U. Assume that on the canonical Z basis it sends every useful source word to a target basis vector with exactly the transported useful-block label, while it kills every non-useful source word. Then the same regrouping descends to the nonhole masks, giving
--
--   $$U_{\mathcal N^{\prime}} \preceq T_{\mathcal N}.$$
--
--   Both masks leave the X and Y spaces whole and project only Z. This theorem is the reusable algebraic bridge from source-order Claim 6.8 data to the grouped broken standard owner consumed by the hole-cover theorem.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Remark 5.1 and Additional Zeroing-Out Step 2, https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Theorems.Thm_mme_basisZAllowedSubtensor_restrict_of_basis_map

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_dwz_source_broken_restrict_of_grouped_basis_router
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (U : TensorObj K 3) {κ : Type u}
    (bU : Basis κ K (U.V 2))
    (label : κ → DWZComponentRestriction.DWZStandardBlock m)
    (transported : DWZSquare.BrokenBlockCopy
      (DWZComponentRestriction.DWZStandardBlock m))
    (blockEquiv : DWZTable2StandardForm.UsefulBlock m outer ≃
      DWZComponentRestriction.DWZStandardBlock m)
    (hTransport : ∀ small,
      blockEquiv small ∈ transported.nonholes ↔
        small ∈ copy.nonholes)
    (f : ∀ i : Fin 3,
      (DWZSourceAligned.coarseAddressObj K outer).V i →ₗ[K] U.V i)
    (hmap : PiTensorProduct.map f
      (DWZSourceAligned.coarseAddressObj K outer).t = U.t)
    (hBasisUseful : ∀ (W : DWZSourceAligned.AddressZWord.{u} outer)
      (hW : DWZSourceAligned.addressWordUseful m outer W),
      ∃ Wg : κ,
        f 2 (DWZSourceAligned.coarseAddressZBasis K outer W) = bU Wg ∧
        label Wg = blockEquiv
          (DWZSourceAligned.addressUsefulBlock m outer W hW))
    (hBasisZero : ∀ W : DWZSourceAligned.AddressZWord.{u} outer,
      ¬ DWZSourceAligned.addressWordUseful m outer W →
        f 2 (DWZSourceAligned.coarseAddressZBasis K outer W) = 0) :
    TensorObj.Restrict
      (U.basisZAllowedSubtensor bU
        (fun Wg ↦ label Wg ∈ transported.nonholes))
      (DWZSourceAligned.brokenAddressObj K m outer copy) := by
  sorry
