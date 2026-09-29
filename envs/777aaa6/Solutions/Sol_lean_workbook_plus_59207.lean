-- Prove2me | solution 1 for lean_workbook_plus_59207
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:43:56.13247+00:00
-- url     : https://prove2.me/submissions/27955d65-5992-4728-a242-012eb85ee051

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a - b) ^ 4 * (a ^ 2 + b ^ 2 + c ^ 2) + (a - b) ^ 2 * (c ^ 2 - a * b) ^ 2 ≥ 0 := by
  (intros; positivity)
