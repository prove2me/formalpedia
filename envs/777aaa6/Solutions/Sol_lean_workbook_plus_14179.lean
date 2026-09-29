-- Prove2me | solution 1 for lean_workbook_plus_14179
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:27.495111+00:00
-- url     : https://prove2.me/submissions/465e7498-0fde-4ab0-92bf-d0a1f2587b54

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) : ∃ a : ℝ, a = (1 / (2 * Real.sqrt 2)) * ((1 + Real.sqrt 2)^n - (1 - Real.sqrt 2)^n) := by
  norm_num
