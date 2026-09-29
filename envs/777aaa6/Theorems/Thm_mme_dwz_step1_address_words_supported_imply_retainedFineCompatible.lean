-- Prove2me | Theorems.Thm_mme_dwz_step1_address_words_supported_imply_retainedFineCompatible
-- name    : mme_dwz_step1_address_words_supported_imply_retainedFineCompatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T21:44:42.293681+00:00
-- url     : https://prove2.me/theorems/822de16d-75f3-46d1-8af2-d73cbfae1093
-- title:
--   DWZ Step-1 filtered source words imply retained fine compatibility
-- statement:
--   Let a retained-owner family have a common coarse Z word. Fix a useful Z basis word for one owner and canonical X and Y basis words for a competitor. If the X and Y words pass the two boundary split-profile filters of Additional Zeroing-Out Step 1, and the three fine words have coordinatewise support in the square CW tensor, then the Z word satisfies the grouped retained-fine compatibility histograms for the competitor. This is the canonical source-word form of Claim 6.2 and restores the X/Y zeroing hypotheses required before Claim 6.8.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Step 1 and Claim 6.2, printed pp. 50--52 (PDF pp. 51--53), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_source_address_filters
import Theorems.Thm_mme_dwz_table2_step1_fine_support_implies_grouped_compatibility
import Theorems.Thm_mme_dwz_table2_completed_fine_words_total_z_histogram
import Definitions.Def_mme_dwz_retained_fine_compatibility

open MME
open MME.DWZStep1Support
open MME.DWZStep1Histogram
open MME.DWZStep2Source

universe u

set_option autoImplicit false

open MME.DWZSourceAligned

theorem mme_dwz_step1_address_words_supported_imply_retainedFineCompatible
    {K : Type u} [Field K]
    (m : ℕ) {Copy : Type u} {N : ℕ}
    (outer : Copy → Fin N → Fin 15)
    (owner competitor : Copy)
    (hCommonZ : ∀ t,
      DWZSquare.shapeZ (outer owner t) =
        DWZSquare.shapeZ (outer competitor t))
    (xWord : AddressModeWord (outer competitor) 0)
    (yWord : AddressModeWord (outer competitor) 1)
    (zWord : AddressZWord (outer owner))
    (hX : addressXWordPassesStep1 m (outer competitor) xWord)
    (hY : addressYWordPassesStep1 m (outer competitor) yWord)
    (hUseful : addressWordUseful m (outer owner) zWord)
    (hSupported : ∀ t,
      (cwSquareFineSplitGrading K 6).blockTensor
        (fun i ↦ fineSplitGrade
          (![addressModeLeftGrade xWord t,
            addressModeLeftGrade yWord t,
            (zWord t).leftGrade] i)
          (![addressModeRightGrade xWord t,
            addressModeRightGrade yWord t,
            (zWord t).rightGrade] i)) ≠ 0) :
    retainedFineCompatible m outer
      (fun t ↦ fineSplitGrade (zWord t).leftGrade (zWord t).rightGrade)
      competitor := by
  sorry
