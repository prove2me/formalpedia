-- Prove2me | solution 1 for lean_workbook_plus_846
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:38.643495+00:00
-- url     : https://prove2.me/submissions/f91f8d14-9f7d-4144-9ada-e663f766ab08

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b : ℝ, a * b = 0 → a = 0 ∨ b = 0 := by
  norm_num
