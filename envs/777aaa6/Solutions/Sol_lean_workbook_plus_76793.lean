-- Prove2me | solution 1 for lean_workbook_plus_76793
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:08:43.303495+00:00
-- url     : https://prove2.me/submissions/c525bae7-bd85-4f90-9b9f-3d851c708b18

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, 4 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥
    (a + b + c) ^ 2 * (2 * (a ^ 2 + b ^ 2 + c ^ 2) - (a * b + b * c + c * a)) +
      (a * b + b * c + c * a) ^ 2 := by
  intro a b c
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
