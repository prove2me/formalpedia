-- Prove2me | solution 1 for lean_workbook_plus_20111
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:03.923014+00:00
-- url     : https://prove2.me/submissions/e6076d41-8bba-4e21-a3aa-b8bd0ae69fca

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : a^2 * (b - c)^2 + b^2 * (c - d)^2 + c^2 * (d - a)^2 + d^2 * (a - b)^2 ≥ 0 := by
  (intros; positivity)
