-- Prove2me | solution 1 for lean_workbook_plus_80599
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:01:18.819029+00:00
-- url     : https://prove2.me/submissions/1d54f750-c539-4244-aeef-9c66f9461f0e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (3 * (a + b) + (a + b) * (b + c) * (c + a) / (a + b + c) - 2 * (a + b + c)) ^ 2 ≥ 0 := by
  (intros; positivity)
