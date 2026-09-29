-- Prove2me | solution 1 for lean_workbook_plus_53984
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:06:10.630282+00:00
-- url     : https://prove2.me/submissions/0ae30082-86c1-4625-a49e-1eba3ba68d28

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^3 + b^3 + c^3 = 3 * a * b * c + (a + b + c) * (a^2 + b^2 + c^2 - a * b - b * c - c * a) := by
  (intros; linarith)
