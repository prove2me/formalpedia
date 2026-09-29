-- Prove2me | solution 1 for lean_workbook_plus_52064
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:11.138134+00:00
-- url     : https://prove2.me/submissions/7b33b0fe-7ebb-4a30-b350-b99b0440b26a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) : 157 + 2 * (a - 1 / 2) ^ 2 + 32 * a ^ 2 * (a ^ 2 - a - 1) ^ 2 + 16 * (a ^ 2 + a - 1) ^ 2 + 18 * a ^ 2 ≥ 0 := by
  (intros; positivity)
