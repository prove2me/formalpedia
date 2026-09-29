-- Prove2me | Theorems.Thm_mme_dwz_broken_owner_x_singleton_zero_of_all_yz_selected_zero
-- name    : mme_dwz_broken_owner_x_singleton_zero_of_all_yz_selected_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T23:28:41.476737+00:00
-- url     : https://prove2.me/theorems/f8b5ad18-2906-4f3d-a772-3222f42a2e84
-- title:
--   Selected Y-Z slices annihilate a rejected X singleton
-- statement:
--   Fix a canonical X-word singleton in one coarse Table-2 address. Suppose that for every canonical Y word and every surviving useful Z word, the tensor slice obtained by applying all three singleton projectors and the broken-copy block maps is zero. Then summing over the full Y basis and over the surviving Z mask shows that the whole broken-copy map annihilates the fixed X singleton. This is the finite-basis expansion needed for Additional Zeroing-Out Step 1.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Steps 1 and 2, printed pp. 51--52 (PDF pp. 52--53), https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_basisZAllowed_map_eq_zero_of_selected_singletons
import Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode
import Definitions.Def_mme_dwz_step1_projector_basis_api

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open MME.DWZSourceAligned

/-- If every surviving Z word and every Y word kills a fixed X singleton,
then the complete Z mask and Y basis sum kill that X singleton. -/

theorem mme_dwz_broken_owner_x_singleton_zero_of_all_yz_selected_zero
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (x : AddressModeWord outer 0)
    (hTripleZero : ∀ (y : AddressModeWord outer 1)
      (z : AddressZWord outer),
      addressWordSurvives m outer copy z →
      let G := brokenAddressGrading K m outer copy
      let sx := DWZComponentRestriction.basisLabelProjection
        (coarseAddressModeBasis K outer 0) id {x}
      let sy := DWZComponentRestriction.basisLabelProjection
        (coarseAddressModeBasis K outer 1) id {y}
      let sz := DWZComponentRestriction.basisLabelProjection
        (coarseAddressZBasis K outer) id {z}
      let selected : ∀ i : Fin 3,
          (coarseAddressObj K outer).V i →ₗ[K]
            (coarseAddressObj K outer).V i :=
        Function.update
          (Function.update
            (Function.update (fun _ ↦ LinearMap.id) 0 sx) 1 sy) 2 sz
      PiTensorProduct.map
        (fun i ↦ (G.blockProj i 0).comp (selected i))
        (coarseAddressObj K outer).t = 0) :
    let G := brokenAddressGrading K m outer copy
    let base : ∀ i : Fin 3,
        (coarseAddressObj K outer).V i →ₗ[K] G.classOf i 0 :=
      fun i ↦ G.blockProj i 0
    let sx := DWZComponentRestriction.basisLabelProjection
      (coarseAddressModeBasis K outer 0) id {x}
    PiTensorProduct.map
      (Function.update base 0 ((base 0).comp sx))
      (coarseAddressObj K outer).t = 0 := by sorry
