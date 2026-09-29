-- Prove2me | solution 1 for lean_workbook_plus_54058
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:45:23.298753+00:00
-- url     : https://prove2.me/submissions/070c3596-f494-4e73-bdf6-db4d203ec8e8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  (a^2 + 2 * b * c) * (b^2 + 2 * c * a) * (c^2 + 2 * a * b) =
  (a^2 + b^2 + c^2) * (a * b + b * c + c * a)^2 - (a - b)^2 * (b - c)^2 * (c - a)^2 := by
  (intros; linarith)
