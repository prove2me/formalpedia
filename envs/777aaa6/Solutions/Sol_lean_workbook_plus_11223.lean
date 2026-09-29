-- Prove2me | solution 1 for lean_workbook_plus_11223
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:47:50.853692+00:00
-- url     : https://prove2.me/submissions/83534418-76e9-4c86-ac58-e1f73a9fd019

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ (n : ℕ), ((n:ℝ) * (1 + 1/n)^n) = n * (1 + 1/n)^n := by
  norm_num
