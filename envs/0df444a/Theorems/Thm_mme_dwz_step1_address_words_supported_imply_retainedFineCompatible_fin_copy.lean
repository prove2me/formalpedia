-- Prove2me | Theorems.Thm_mme_dwz_step1_address_words_supported_imply_retainedFineCompatible_fin_copy
-- name    : mme_dwz_step1_address_words_supported_imply_retainedFineCompatible_fin_copy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T02:44:58.658405+00:00
-- url     : https://prove2.me/theorems/d4cd595b-8702-405b-8ccb-11a93734113c
-- title:
--   Claim 6.2 compatibility for finite outer-copy families over arbitrary fields
-- statement:
--   For a finite family of outer Table-2 words indexed by Fin n over a field in any universe, common coarse Z shapes, Step-1-admissible X/Y words, a useful Z word, and coordinatewise fine CW support imply the retained fine compatibility conclusion of DWZ Claim 6.2. This is the accepted Claim-6.2 theorem transported through ULift so the finite owner index does not have to share the coefficient field's universe.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.1, Claim 6.2 and Additional Zeroing-Out Step 1, printed pp. 51--52 / PDF pp. 52--53; https://arxiv.org/abs/2210.10173. This statement is the finite-index universe-polymorphic interface to the already accepted formalization of that claim.

import Theorems.Thm_mme_dwz_step1_address_words_supported_imply_retainedFineCompatible

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u

set_option autoImplicit false

open MME.DWZSourceAligned

theorem mme_dwz_step1_address_words_supported_imply_retainedFineCompatible_fin_copy
    {K : Type u} [Field K]
    (m : ℕ) {n N : ℕ}
    (outer : Fin n → Fin N → Fin 15)
    (owner competitor : Fin n)
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
