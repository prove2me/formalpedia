-- Prove2me | solution 1 for lean_workbook_plus_30444
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:05.580972+00:00
-- url     : https://prove2.me/submissions/e4e2cf3a-bd40-4fd4-a751-ab0602b90fe6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf : ∀ x, 2 * f (f x) - Real.sqrt 2 * f x = x) : ∃ a, f 0 = a := by
  norm_num
