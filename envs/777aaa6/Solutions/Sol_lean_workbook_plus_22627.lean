-- Prove2me | solution 1 for lean_workbook_plus_22627
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:09.0964+00:00
-- url     : https://prove2.me/submissions/b5507567-0c90-4ce4-b51d-6b35de1289a1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 1 * 3 + 2 * 2 + 3 * 1 = 10) : 1 * 3 + 2 * 2 + 3 * 1 = 10 := by
  norm_num
