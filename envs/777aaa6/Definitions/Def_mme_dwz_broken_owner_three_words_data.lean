-- Prove2me | Definitions.Def_mme_dwz_broken_owner_three_words_data
-- name    : mme_dwz_broken_owner_three_words_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-28T10:48:09.436286+00:00
-- url     : https://prove2.me/theorems/0461d6ab-b758-4694-9392-c8b69f9bd9ca
-- title:
--   Selected three-word data for one broken DWZ owner
-- statement:
--   For a fixed coarse address and one broken owner, this module packages a selected canonical X word, Y word, and Z word as a dependent three-mode word. It records both the dependent and literal-update presentations of their singleton projectors and block-projected maps, together with the corresponding fine-grade family at one coordinate. These are representation data for Additional Zeroing-Out Step 1, not an additional mathematical hypothesis.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_projector_basis_api
import Definitions.Def_mme_dwz_cw_square_fine_split_grading

open MME Module

universe u

set_option autoImplicit false

namespace MME.DWZSourceAligned

def brokenOwnerThreeWordsWord
    {N : ℕ} {outer : Fin N → Fin 15}
    (x : AddressModeWord outer 0)
    (y : AddressModeWord outer 1)
    (z : AddressZWord outer) :
    ∀ i : Fin 3, AddressModeWord outer i :=
  Fin.cases x
    (Fin.cases y (Fin.cases z (fun j : Fin 0 ↦ Fin.elim0 j)))

noncomputable def brokenOwnerThreeWordsSelectedProjector
    (K : Type u) [Field K]
    {N : ℕ} (outer : Fin N → Fin 15)
    (x : AddressModeWord outer 0)
    (y : AddressModeWord outer 1)
    (z : AddressZWord outer) :
    ∀ i : Fin 3,
      (coarseAddressObj K outer).V i →ₗ[K]
        (coarseAddressObj K outer).V i :=
  Function.update
    (Function.update
      (Function.update (fun _ ↦ LinearMap.id) 0
        (DWZComponentRestriction.basisLabelProjection
          (coarseAddressModeBasis K outer 0) id {x})) 1
        (DWZComponentRestriction.basisLabelProjection
          (coarseAddressModeBasis K outer 1) id {y})) 2
        (DWZComponentRestriction.basisLabelProjection
          (coarseAddressZBasis K outer) id {z})

noncomputable def brokenOwnerThreeWordsWordMap
    (K : Type u) [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (x : AddressModeWord outer 0)
    (y : AddressModeWord outer 1)
    (z : AddressZWord outer) :
    ∀ i : Fin 3,
      (coarseAddressObj K outer).V i →ₗ[K]
        (brokenAddressObj K m outer copy).V i :=
  fun i ↦ ((brokenAddressGrading K m outer copy).blockProj i 0).comp
    (DWZComponentRestriction.basisLabelProjection
      (coarseAddressModeBasis K outer i) id
      {brokenOwnerThreeWordsWord x y z i})

noncomputable def brokenOwnerThreeWordsSelectedMap
    (K : Type u) [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (x : AddressModeWord outer 0)
    (y : AddressModeWord outer 1)
    (z : AddressZWord outer) :
    ∀ i : Fin 3,
      (coarseAddressObj K outer).V i →ₗ[K]
        (brokenAddressObj K m outer copy).V i :=
  fun i ↦ ((brokenAddressGrading K m outer copy).blockProj i 0).comp
    (brokenOwnerThreeWordsSelectedProjector K outer x y z i)

def brokenOwnerThreeWordsFineGradeFamily
    {N : ℕ} {outer : Fin N → Fin 15}
    (x : AddressModeWord outer 0)
    (y : AddressModeWord outer 1)
    (z : AddressZWord outer) (r : Fin N) :
    Fin 3 → Fin (3 * 3) :=
  fun i ↦ MME.DWZStep1Support.fineSplitGrade
    (brokenOwnerThreeWordsWord x y z i r).leftGrade
    (brokenOwnerThreeWordsWord x y z i r).rightGrade

def brokenOwnerThreeWordsVectorFineGradeFamily
    {N : ℕ} {outer : Fin N → Fin 15}
    (x : AddressModeWord outer 0)
    (y : AddressModeWord outer 1)
    (z : AddressZWord outer) (r : Fin N) :
    Fin 3 → Fin (3 * 3) :=
  ![
    MME.DWZStep1Support.fineSplitGrade
      (addressModeLeftGrade x r) (addressModeRightGrade x r),
    MME.DWZStep1Support.fineSplitGrade
      (addressModeLeftGrade y r) (addressModeRightGrade y r),
    MME.DWZStep1Support.fineSplitGrade
      (z r).leftGrade (z r).rightGrade]

end MME.DWZSourceAligned


