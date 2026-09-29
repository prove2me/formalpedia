-- Prove2me | solution 1 for lean_workbook_plus_25072
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:18:57.19213+00:00
-- url     : https://prove2.me/submissions/15b71f19-6fe6-4377-86cb-a4f365547d5c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a ≥ 1, (3 * a - 5) ^ 2 * ((10 * a ^ 2 + 8 * a) * (4 * a - 3) ^ 2 + 21 * (a - 1) ^ 2 + 2 * a ^ 4 + 4 * a ^ 3 + 4) ≥ 0 := by
  norm_num
