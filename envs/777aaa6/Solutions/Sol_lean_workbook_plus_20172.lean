-- Prove2me | solution 1 for lean_workbook_plus_20172
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:55:36.817849+00:00
-- url     : https://prove2.me/submissions/cae5a0a2-0dd3-4eef-a6e3-eae274b7ae7e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  (intros; ring)
