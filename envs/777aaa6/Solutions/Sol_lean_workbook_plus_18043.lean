-- Prove2me | solution 1 for lean_workbook_plus_18043
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:06.585327+00:00
-- url     : https://prove2.me/submissions/5b2536d6-18a2-49d0-a158-0d5a19468ae1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2 - c^2 - 2 * a * b + b * c + a * c)^2 + (b^2 - a^2 - 2 * b * c + a * b + a * c)^2 + (c^2 - b^2 - 2 * a * c + a * b + b * c)^2 ≥ 0 := by
  (intros; positivity)
