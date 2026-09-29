-- Prove2me | solution 1 for lean_workbook_plus_59728
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:44.265299+00:00
-- url     : https://prove2.me/submissions/84fb907c-3fbc-4e58-b123-005ebebbf0b4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a t : ℝ) : (a - 10) * t + a * t = 390 ↔ (2 * a - 10) * t = 390 := by
  (intros; ring)
