-- Prove2me | solution 1 for lean_workbook_plus_1011
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:42.039252+00:00
-- url     : https://prove2.me/submissions/f866ffe9-681c-4b69-af1c-3024a68a9873

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (c x : ℝ) (hc : 0 < c) (hx : |x| < c) : ∃ y : ℝ, y = ∑' k : ℕ, a k * x ^ k := by
  norm_num
