-- Prove2me | solution 1 for lean_workbook_plus_5786
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:34:15.657131+00:00
-- url     : https://prove2.me/submissions/0de71a0c-086d-4a78-96a4-63d78ef82404

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a < 1, 4 * (2 * a ^ 4 + 1) * (a ^ 2 + 2) ≥ a ^ 2 * (2 * a + 1) ^ 7 * (a + 1) ^ 2 := by
  norm_num
