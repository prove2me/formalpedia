-- Prove2me | solution 1 for lean_workbook_plus_69452
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:16.961022+00:00
-- url     : https://prove2.me/submissions/1ac43beb-298c-45ea-8aac-56b732f723ed

import Mathlib

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a + b = c) : a ^ 2 + b ^ 2 ≥ c ^ 2 / 2 := by
  rw [← hab]
  nlinarith [sq_nonneg (a - b)]
