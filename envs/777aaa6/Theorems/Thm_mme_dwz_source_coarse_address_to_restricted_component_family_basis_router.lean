-- Prove2me | Theorems.Thm_mme_dwz_source_coarse_address_to_restricted_component_family_basis_router
-- name    : mme_dwz_source_coarse_address_to_restricted_component_family_basis_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:36:29.643361+00:00
-- url     : https://prove2.me/theorems/09f89a1c-9e24-4b2b-89c6-1daa5437fd73
-- title:
--   Exact source-address router to the fifteen restricted Table-2 components
-- statement:
--   Let a source address have the exact Table-2 row histogram at a positive scale $m$. Then it admits modewise linear maps to the ordered Kronecker product of the fifteen restricted Table-2 component powers, and these maps preserve the literal tensor. Every useful source $Z$-basis word is sent exactly to a grouped available-word basis vector whose fine $Z$ label agrees position-by-position with the source label. Every non-useful source basis word is sent to zero. Thus this theorem packages both branches of the source-to-standard basis router needed for the broken-copy restriction.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2--5.5, Table 2, and the component restrictions in Sections 6.2--6.3; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_restricted_component_z_basis
import Definitions.Def_mme_dwz_source_aligned_broken_obj

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_dwz_source_coarse_address_to_restricted_component_family_basis_router
    {K : Type u} [Field K] {N m : ℕ}
    (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        MME.DWZTable2Counts.component s * m)
    (hm : 0 < m) :
    ∃ e : MME.DWZComponentRestriction.GroupedPosition m ≃ Fin N,
      (∀ p, outer (e p) =
        MME.DWZComponentRestriction.groupedOuter p) ∧
      ∃ f : ∀ i : Fin 3,
          (MME.DWZSourceAligned.coarseAddressObj K outer).V i →ₗ[K]
            (MME.TensorObj.kronFin 15 (fun s ↦
              MME.DWZComponentRestriction.restrictedComponentPower K s m)).V i,
        PiTensorProduct.map f
            (MME.DWZSourceAligned.coarseAddressObj K outer).t =
          (MME.TensorObj.kronFin 15 (fun s ↦
            MME.DWZComponentRestriction.restrictedComponentPower K s m)).t ∧
        (∀ (W : MME.DWZSourceAligned.AddressZWord.{u} outer)
          (_hW : MME.DWZSourceAligned.addressWordUseful m outer W),
          ∃ Wg : MME.DWZComponentRestriction.GroupedAllowedWords.{u} m,
            f 2 (MME.DWZSourceAligned.coarseAddressZBasis K outer W) =
              MME.TensorObj.kronFinModePiBasis 15
                (fun s ↦
                  MME.DWZComponentRestriction.restrictedComponentPower K s m) 2
                (fun s ↦
                  MME.DWZComponentRestriction.restrictedComponentZBasis K s m) Wg ∧
            ∀ p, MME.DWZComponentRestriction.groupedFineZ Wg p =
              MME.DWZSourceAligned.addressFineZ W (e p)) ∧
        ∀ W : MME.DWZSourceAligned.AddressZWord.{u} outer,
          ¬ MME.DWZSourceAligned.addressWordUseful m outer W →
            f 2 (MME.DWZSourceAligned.coarseAddressZBasis K outer W) = 0 := by
  sorry
