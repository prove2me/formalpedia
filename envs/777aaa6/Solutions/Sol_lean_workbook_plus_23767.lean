-- Prove2me | solution 1 for lean_workbook_plus_23767
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:46:44.045061+00:00
-- url     : https://prove2.me/submissions/709cf0d4-3cdf-4e49-aa36-d791d0154c8b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * (a - 1) ^ 2 + 3 * (b - 1) ^ 2 + 3 * (c - 1) ^ 2 >= 0 := by
  (intros; positivity)
