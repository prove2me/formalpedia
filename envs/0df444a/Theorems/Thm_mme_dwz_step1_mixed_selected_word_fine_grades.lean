-- Prove2me | Theorems.Thm_mme_dwz_step1_mixed_selected_word_fine_grades
-- name    : mme_dwz_step1_mixed_selected_word_fine_grades
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T11:27:11.7847+00:00
-- url     : https://prove2.me/theorems/14aa50e1-56f7-47d0-9df3-83fb074608ff
-- title:
--   Fine grades of the mixed selected X/Y/Z word
-- statement:
--   The modewise fine grade of the mixed selected word is exactly the three-vector formed from the competitor's chosen X and Y address grades and the owner's chosen Z address grade.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data

open MME Module

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZStep1Support
open MME.DWZGlobalCorrelated

theorem mme_dwz_step1_mixed_selected_word_fine_grades
    {K : Type u} [Field K]
    {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1)
    (r : Fin L) :
    (fun i ↦ MME.DWZStep1Support.fineSplitGrade
      ((step1MixedSelectedWord reindex edge competitor owner W x y i r).leftGrade)
      ((step1MixedSelectedWord reindex edge competitor owner W x y i r).rightGrade)) =
    (fun i ↦ MME.DWZStep1Support.fineSplitGrade
      (![addressModeLeftGrade x r,
        addressModeLeftGrade y r,
        (W r).leftGrade] i)
      (![addressModeRightGrade x r,
        addressModeRightGrade y r,
        (W r).rightGrade] i)) := by
  sorry
