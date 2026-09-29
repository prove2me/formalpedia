-- Prove2me | solution 1 for lean_workbook_plus_21758
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:35.114451+00:00
-- url     : https://prove2.me/submissions/9c73d1ff-0540-43fb-a7f4-3fe15cc6d03a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^2 * (b - c)^2 + b^2 * (c - a)^2 + c^2 * (a - b)^2 ≥ 0 := by
  (intros; positivity)
