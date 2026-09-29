-- Prove2me | solution 1 for lean_workbook_plus_52181
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:02.835712+00:00
-- url     : https://prove2.me/submissions/b5437971-33ee-4359-9a70-c2f6b3b827f8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 8 * (b - c) ^ 2 * (a - c) ^ 2 * (a - b) ^ 2 + (a ^ 2 * b + a ^ 2 * c + a * b ^ 2 - 6 * a * b * c + a * c ^ 2 + b ^ 2 * c + b * c ^ 2) ^ 2 ≥ 0 := by
  (intros; positivity)
