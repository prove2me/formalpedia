-- Prove2me | solution 1 for lean_workbook_plus_43695
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:03.197049+00:00
-- url     : https://prove2.me/submissions/6cb1c561-8bf2-42b0-9d6a-ea6b06463ea6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 ≥ 0 := by
  (intros; positivity)
