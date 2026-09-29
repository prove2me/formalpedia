-- Prove2me | solution 1 for lean_workbook_plus_43792
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:58.078607+00:00
-- url     : https://prove2.me/submissions/76c39dee-2ecd-4a99-8159-ab6a2c0df0fb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 >= 0 := by
  (intros; positivity)
