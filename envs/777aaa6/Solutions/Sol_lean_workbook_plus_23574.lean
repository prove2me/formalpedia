-- Prove2me | solution 1 for lean_workbook_plus_23574
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:02.926016+00:00
-- url     : https://prove2.me/submissions/46fd5c75-8f8d-4b57-8e7b-0ff7b49d0c7c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℚ) (hx : x = 32 / 15) : x = 32 / 15 := by
  (intros; simp_all)
