-- Prove2me | Theorems.Thm_mme_dwz_broken_owner_y_singleton_zero_of_all_xz_selected_zero
-- name    : mme_dwz_broken_owner_y_singleton_zero_of_all_xz_selected_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T23:34:48.146882+00:00
-- url     : https://prove2.me/theorems/9f9fe61f-fe7d-4d81-9011-05990a1e17e6
-- title:
--   Step-1 X filtering reduces a rejected Y owner slice to selected X-Z singletons
-- statement:
--   Fix one coarse address owner and one canonical Y-address word. Assume that every tensor slice obtained by pairing this Y word with an X word accepted by the Step-1 boundary filter and a Z word retained by the broken-copy mask is zero after projection to the broken component. Then the entire slice selected by that Y word is zero after applying the complete Step-1 X filter and the complete retained-Z mask. This basis-expansion lemma isolates the algebraic part of the paper's Step-1 diagonal argument.

import Theorems.Thm_mme_basisZAllowed_map_eq_zero_of_selected_singletons
import Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode
import Definitions.Def_mme_dwz_step1_projector_basis_api

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

open MME.DWZSourceAligned

theorem mme_dwz_broken_owner_y_singleton_zero_of_all_xz_selected_zero
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (y : AddressModeWord outer 1)
    (hTripleZero : ∀ (x : AddressModeWord outer 0),
      addressXWordPassesStep1 m outer x →
      ∀ (z : AddressZWord outer),
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
    let xMaps := Function.update base 0
      ((base 0).comp (addressXStep1Projector K m outer))
    let sy := DWZComponentRestriction.basisLabelProjection
      (coarseAddressModeBasis K outer 1) id {y}
    PiTensorProduct.map
      (Function.update xMaps 1 ((xMaps 1).comp sy))
      (coarseAddressObj K outer).t = 0 := by
  sorry
