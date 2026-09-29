-- Prove2me | solution 1 for lean_workbook_plus_26791
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:25:19.538762+00:00
-- url     : https://prove2.me/submissions/503f87c5-6ecb-4b2c-be45-1add88bde845

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (x: ℝ) (hf: f x = x) (hx: 0 < x ∧ x <= 1) : ∃ y, y = x := by
  norm_num
