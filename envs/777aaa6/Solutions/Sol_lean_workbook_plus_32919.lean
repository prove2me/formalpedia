-- Prove2me | solution 1 for lean_workbook_plus_32919
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:06:03.597812+00:00
-- url     : https://prove2.me/submissions/045778e4-98c7-42ad-a47c-3b3b0794201f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 ≥ 0 := by
  (intros; positivity)
