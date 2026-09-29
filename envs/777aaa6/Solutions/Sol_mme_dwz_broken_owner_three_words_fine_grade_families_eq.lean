-- Prove2me | solution 1 for mme_dwz_broken_owner_three_words_fine_grade_families_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T10:59:47.178974+00:00
-- url     : https://prove2.me/submissions/ee30ed18-d483-4700-9fb4-af06732747b5

import Definitions.Def_mme_dwz_broken_owner_three_words_data

open MME Module
open MME.DWZSourceAligned

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {N : ℕ} {outer : Fin N → Fin 15}
    (x : AddressModeWord outer 0)
    (y : AddressModeWord outer 1)
    (z : AddressZWord outer) (r : Fin N) :
    brokenOwnerThreeWordsFineGradeFamily x y z r =
      brokenOwnerThreeWordsVectorFineGradeFamily x y z r := by
  funext i
  fin_cases i <;> rfl
