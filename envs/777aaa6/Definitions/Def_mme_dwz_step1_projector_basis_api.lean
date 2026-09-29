-- Prove2me | Definitions.Def_mme_dwz_step1_projector_basis_api
-- name    : mme_dwz_step1_projector_basis_api
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T22:48:55.457681+00:00
-- url     : https://prove2.me/theorems/58ad06e7-f236-4ac4-9c76-df12357ec828
-- title:
--   Canonical basis action of the DWZ Step-1 source projectors
-- statement:
--   The source-address X and Y projectors for Additional Zeroing-Out Step 1 act diagonally on the canonical coarse-address word bases: an accepted word is fixed and a rejected word is sent to zero. Consequently, each accepted singleton basis projector is absorbed by the corresponding Step-1 projector. The module also records the definitional identification of the arbitrary-mode address basis in mode Z with the existing source-aligned Z-word basis.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Step 1, printed p. 51 (PDF p. 52), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_source_address_projectors

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZSourceAligned

/-- The arbitrary-mode address basis specializes definitionally to the
existing source-aligned Z-word basis in mode two. -/
theorem coarseAddressModeBasis_two_eq_Z
    {K : Type u} [Field K] {N : ℕ} (outer : Fin N → Fin 15) :
    coarseAddressModeBasis K outer 2 = coarseAddressZBasis K outer := by
  rfl

/-- The literal Step-1 X projector fixes every accepted canonical address
word. -/
theorem addressXStep1Projector_apply_basis_of_passes
    {K : Type u} [Field K] (m : ℕ) {N : ℕ}
    (outer : Fin N → Fin 15) (x : AddressModeWord outer 0)
    (hx : addressXWordPassesStep1 m outer x) :
    addressXStep1Projector K m outer
        (coarseAddressModeBasis K outer 0 x) =
      coarseAddressModeBasis K outer 0 x := by
  classical
  simp only [addressXStep1Projector,
    DWZComponentRestriction.basisLabelProjection,
    Module.Basis.constr_basis, id_eq, Finset.mem_filter,
    Finset.mem_univ, true_and, hx, if_true]

/-- The literal Step-1 X projector kills every rejected canonical address
word. -/
theorem addressXStep1Projector_apply_basis_of_not_passes
    {K : Type u} [Field K] (m : ℕ) {N : ℕ}
    (outer : Fin N → Fin 15) (x : AddressModeWord outer 0)
    (hx : ¬ addressXWordPassesStep1 m outer x) :
    addressXStep1Projector K m outer
        (coarseAddressModeBasis K outer 0 x) = 0 := by
  classical
  simp only [addressXStep1Projector,
    DWZComponentRestriction.basisLabelProjection,
    Module.Basis.constr_basis, id_eq, Finset.mem_filter,
    Finset.mem_univ, true_and, hx, if_false]

/-- On an accepted X word, the Step-1 projector absorbs the corresponding
singleton projector. -/
theorem addressXStep1Projector_comp_singleton_of_passes
    {K : Type u} [Field K] (m : ℕ) {N : ℕ}
    (outer : Fin N → Fin 15) (x : AddressModeWord outer 0)
    (hx : addressXWordPassesStep1 m outer x) :
    (addressXStep1Projector K m outer).comp
        (DWZComponentRestriction.basisLabelProjection
          (coarseAddressModeBasis K outer 0) id {x}) =
      DWZComponentRestriction.basisLabelProjection
        (coarseAddressModeBasis K outer 0) id {x} := by
  classical
  apply (coarseAddressModeBasis K outer 0).ext
  intro a
  by_cases ha : a = x
  · subst a
    simp only [LinearMap.comp_apply,
      addressXStep1Projector_apply_basis_of_passes m outer x hx,
      DWZComponentRestriction.basisLabelProjection,
      Module.Basis.constr_basis, id_eq, Finset.mem_singleton, if_true]
  · simp only [LinearMap.comp_apply,
      DWZComponentRestriction.basisLabelProjection,
      Module.Basis.constr_basis, id_eq, Finset.mem_singleton,
      if_neg ha, map_zero]

/-- The literal Step-1 Y projector fixes every accepted canonical address
word. -/
theorem addressYStep1Projector_apply_basis_of_passes
    {K : Type u} [Field K] (m : ℕ) {N : ℕ}
    (outer : Fin N → Fin 15) (y : AddressModeWord outer 1)
    (hy : addressYWordPassesStep1 m outer y) :
    addressYStep1Projector K m outer
        (coarseAddressModeBasis K outer 1 y) =
      coarseAddressModeBasis K outer 1 y := by
  classical
  simp only [addressYStep1Projector,
    DWZComponentRestriction.basisLabelProjection,
    Module.Basis.constr_basis, id_eq, Finset.mem_filter,
    Finset.mem_univ, true_and, hy, if_true]

/-- The literal Step-1 Y projector kills every rejected canonical address
word. -/
theorem addressYStep1Projector_apply_basis_of_not_passes
    {K : Type u} [Field K] (m : ℕ) {N : ℕ}
    (outer : Fin N → Fin 15) (y : AddressModeWord outer 1)
    (hy : ¬ addressYWordPassesStep1 m outer y) :
    addressYStep1Projector K m outer
        (coarseAddressModeBasis K outer 1 y) = 0 := by
  classical
  simp only [addressYStep1Projector,
    DWZComponentRestriction.basisLabelProjection,
    Module.Basis.constr_basis, id_eq, Finset.mem_filter,
    Finset.mem_univ, true_and, hy, if_false]

/-- On an accepted Y word, the Step-1 projector absorbs the corresponding
singleton projector. -/
theorem addressYStep1Projector_comp_singleton_of_passes
    {K : Type u} [Field K] (m : ℕ) {N : ℕ}
    (outer : Fin N → Fin 15) (y : AddressModeWord outer 1)
    (hy : addressYWordPassesStep1 m outer y) :
    (addressYStep1Projector K m outer).comp
        (DWZComponentRestriction.basisLabelProjection
          (coarseAddressModeBasis K outer 1) id {y}) =
      DWZComponentRestriction.basisLabelProjection
        (coarseAddressModeBasis K outer 1) id {y} := by
  classical
  apply (coarseAddressModeBasis K outer 1).ext
  intro a
  by_cases ha : a = y
  · subst a
    simp only [LinearMap.comp_apply,
      addressYStep1Projector_apply_basis_of_passes m outer y hy,
      DWZComponentRestriction.basisLabelProjection,
      Module.Basis.constr_basis, id_eq, Finset.mem_singleton, if_true]
  · simp only [LinearMap.comp_apply,
      DWZComponentRestriction.basisLabelProjection,
      Module.Basis.constr_basis, id_eq, Finset.mem_singleton,
      if_neg ha, map_zero]

end MME.DWZSourceAligned


