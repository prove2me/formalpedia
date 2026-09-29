-- Prove2me | solution 1 for lean_workbook_plus_13122
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:32:23.323787+00:00
-- url     : https://prove2.me/submissions/5005eb88-ae91-4156-b2fe-71f5863a4d17

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a + b - c - Real.sqrt ((a + c - b) * (b + c - a))) ^ 2 ≥ 0 := by
  (intros; positivity)
