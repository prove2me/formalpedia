-- Prove2me | Theorems.Thm_mme_dwz_source_broken_owner_restrict_grouped_standard
-- name    : mme_dwz_source_broken_owner_restrict_grouped_standard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:45:59.981168+00:00
-- url     : https://prove2.me/theorems/d4b1005f-e7a7-4cff-b685-6b93caed6d17
-- title:
--   A source broken owner restricts to a grouped Table-2 broken standard copy
-- statement:
--   Fix a source-order Table-2 address with the exact row histogram at positive scale $m$, and retain any broken copy of its useful blocks. Then there is a broken copy on the canonical grouped Table-2 block type with exactly the same number of nonholes. The corresponding literal grouped restricted-component tensor, projected to those transported nonholes, is a restriction of the source broken-address tensor. This is the per-owner source packaging needed before assembling different retained owners by a direct-sum map.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.5, Lemma 5.6, Table 2, and Sections 6.2--6.3; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Definitions.Def_mme_dwz_source_aligned_broken_obj

open MME Module

universe u

set_option autoImplicit false

theorem mme_dwz_source_broken_owner_restrict_grouped_standard
    {K : Type u} [Field K] {N m : ℕ}
    (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        MME.DWZTable2Counts.component s * m)
    (hm : 0 < m)
    (copy : MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m outer)) :
    ∃ transported : MME.DWZSquare.BrokenBlockCopy
        (MME.DWZComponentRestriction.DWZStandardBlock m),
      transported.nonholes.card = copy.nonholes.card ∧
      MME.TensorObj.Restrict
        ((MME.TensorObj.kronFin 15 (fun s ↦
            MME.DWZComponentRestriction.restrictedComponentPower K s m)).basisZAllowedSubtensor
          (MME.TensorObj.kronFinModePiBasis 15
            (fun s ↦
              MME.DWZComponentRestriction.restrictedComponentPower K s m) 2
            (fun s ↦
              MME.DWZComponentRestriction.restrictedComponentZBasis K s m))
          (fun Wg ↦ MME.DWZComponentRestriction.groupedUsefulBlock m Wg ∈
            transported.nonholes))
        (MME.DWZSourceAligned.brokenAddressObj K m outer copy) := by
  sorry
