-- Prove2me | Theorems.Thm_mme_dwz_broken_owner_three_words_fine_grade_families_eq
-- name    : mme_dwz_broken_owner_three_words_fine_grade_families_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:50:18.569448+00:00
-- url     : https://prove2.me/theorems/49c0a317-7f7d-4880-aaa8-e8ae80bdfc9b
-- title:
--   Dependent and vector fine grades agree for three selected owner words
-- statement:
--   The fine-grade family obtained from the dependent three-mode packaging of selected X, Y, and Z address words agrees with the literal three-entry vector of their fine grades at every coordinate. This identifies two presentations of the same Step-1 selection data.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_broken_owner_three_words_data

open MME Module
open MME.DWZSourceAligned

set_option autoImplicit false

theorem mme_dwz_broken_owner_three_words_fine_grade_families_eq
    {N : ℕ} {outer : Fin N → Fin 15}
    (x : AddressModeWord outer 0)
    (y : AddressModeWord outer 1)
    (z : AddressZWord outer) (r : Fin N) :
    brokenOwnerThreeWordsFineGradeFamily x y z r =
      brokenOwnerThreeWordsVectorFineGradeFamily x y z r := by
  sorry
