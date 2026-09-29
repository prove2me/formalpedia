-- Prove2me | Theorems.Thm_mme_dwz_arbitrary_coarse_address_selected_word_zero_of_coordinate
-- name    : mme_dwz_arbitrary_coarse_address_selected_word_zero_of_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T11:17:22.764892+00:00
-- url     : https://prove2.me/theorems/248353e4-b9bc-44bf-89ba-ceb24305a8ff
-- title:
--   A zero fine coordinate kills an arbitrary mixed coarse-address word
-- statement:
--   For an arbitrary per-mode coarse address in a squared Coppersmith--Winograd power, a selected lifted coarse-pair word is annihilated after arbitrary postmaps whenever its fine block tensor vanishes in one coordinate. This is the mixed-address analogue of the proved standard-address coordinate support theorem.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem mme_dwz_arbitrary_coarse_address_selected_word_zero_of_coordinate
    {K : Type u} [Field K] {N : ℕ}
    (address : Fin 3 → Fin N → Fin 5)
    (selected : ∀ i r,
      DWZComponentRestriction.LiftedCoarsePair.{u} 6 (address i r))
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i,
      (gradedAddressBlock (cwSquareCanonicalGrading K 6) address).V i →ₗ[K]
        W i)
    (r : Fin N)
    (hzero : (cwSquareFineSplitGrading K 6).blockTensor
      (fun i ↦ fineSplitGrade
        (selected i r).leftGrade (selected i r).rightGrade) = 0) :
    PiTensorProduct.map
        (fun i ↦ (post i).comp
          (DWZComponentRestriction.basisLabelProjection
            (arbitraryCoarseAddressModeBasis K address i) id {selected i}))
        (gradedAddressBlock (cwSquareCanonicalGrading K 6) address).t = 0 := by
  sorry
