-- Prove2me | solution 1 for lean_workbook_plus_1400
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:23:52.079305+00:00
-- url     : https://prove2.me/submissions/febe6c2e-4fd3-4ac9-b63c-ce02c051f9b7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (ha : a ≤ 0) : ∀ x : ℝ, ∃ y : ℝ, y = a * x ^ 2 := by
  norm_num
