-- Prove2me | solution 1 for lean_workbook_plus_39055
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:50.799423+00:00
-- url     : https://prove2.me/submissions/b5476dbf-e459-4d8c-9254-517df6dad7d1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (e : ℝ) (x : ℝ) (h₁ : 4 * x + 3 * x = 1 / 2 * e) (h₂ : e = 500) : x = 1 / 14 * 500 := by
  (intros; linarith)
