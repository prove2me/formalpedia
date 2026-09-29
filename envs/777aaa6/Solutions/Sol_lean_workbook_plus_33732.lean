-- Prove2me | solution 1 for lean_workbook_plus_33732
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:26.151615+00:00
-- url     : https://prove2.me/submissions/b6654934-a30e-4c06-a707-b2a46284147d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a - 2) ^ 2 * (a + 1) ^ 2 + (b - 2) ^ 2 * (b + 1) ^ 2 + (c - 2) ^ 2 * (c + 1) ^ 2 ≥ 0 := by
  (intros; positivity)
