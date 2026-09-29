-- Prove2me | solution 1 for lean_workbook_plus_8309
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:59:06.209448+00:00
-- url     : https://prove2.me/submissions/968ab5de-87b7-4b9c-9bed-d3517820ab2f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k : ℝ) : (1 / 3 * (9 * k / 2 * 3 * k / 2) * Real.sqrt 3 / 2 * 9 * k) = 81 * Real.sqrt 3 / 8 * k ^ 3 := by
  (intros; linarith)
