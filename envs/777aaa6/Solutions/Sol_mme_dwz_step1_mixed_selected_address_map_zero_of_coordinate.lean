-- Prove2me | solution 1 for mme_dwz_step1_mixed_selected_address_map_zero_of_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:31:53.910569+00:00
-- url     : https://prove2.me/submissions/cc0ba1fc-878a-4e16-872d-1daa281bc99b

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data
import Theorems.Thm_mme_dwz_arbitrary_coarse_address_selected_word_zero_of_coordinate
import Theorems.Thm_mme_dwz_step1_mixed_selected_word_fine_grades

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 14000

open MME.DWZSourceAligned
open MME.DWZStep1Support
open MME.DWZGlobalCorrelated

private theorem blockTensor_eq_zero_of_address_eq
    {K : Type u} [Field K] {T : TensorObj K 3} {t : ℕ}
    (G : T.TypeGrading t) {σ τ : Fin 3 → Fin t}
    (hστ : σ = τ) (hzero : G.blockTensor τ = 0) :
    G.blockTensor σ = 0 := by
  subst τ
  exact hzero

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1)
    (r : Fin L)
    (hFineZero : (cwSquareFineSplitGrading K 6).blockTensor
      (fun i ↦ MME.DWZStep1Support.fineSplitGrade
        (![addressModeLeftGrade x r,
          addressModeLeftGrade y r,
          (W r).leftGrade] i)
        (![addressModeRightGrade x r,
          addressModeRightGrade y r,
          (W r).rightGrade] i)) = 0) :
    PiTensorProduct.map
      (step1MixedSelectedAddressMaps K m reindex q edge
        competitor owner W x y)
      (gradedAddressBlock (cwSquareCanonicalGrading K 6)
        (step1MixedAddress reindex edge competitor owner)).t = 0 := by
  let address := step1MixedAddress reindex edge competitor owner
  let selected := step1MixedSelectedWord reindex edge competitor owner W x y
  let post := step1MixedFilteredAddressPost K m reindex q edge competitor owner
  apply mme_dwz_arbitrary_coarse_address_selected_word_zero_of_coordinate
    (K := K) address selected post r
  change (cwSquareFineSplitGrading K 6).blockTensor
      (fun i ↦ MME.DWZStep1Support.fineSplitGrade
        ((step1MixedSelectedWord reindex edge competitor owner W x y i r).leftGrade)
        ((step1MixedSelectedWord reindex edge competitor owner W x y i r).rightGrade)) = 0
  exact blockTensor_eq_zero_of_address_eq
    (cwSquareFineSplitGrading K 6)
    (mme_dwz_step1_mixed_selected_word_fine_grades
      (K := K) reindex edge competitor owner W x y r)
    hFineZero
