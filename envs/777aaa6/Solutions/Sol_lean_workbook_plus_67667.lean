-- Prove2me | solution 1 for lean_workbook_plus_67667
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:20.044285+00:00
-- url     : https://prove2.me/submissions/d5620001-7700-4d4e-be02-a9c563716d1e

import Mathlib

set_option autoImplicit false

theorem solution : ∀ x : ℝ, 0 < x ∧ x < 1 → 0 < 56 * x ^ 2 ∧ 56 * x ^ 2 < 56 := by
  intro x hx
  have hx0 : 0 < x := hx.1
  constructor
  · positivity
  · nlinarith [mul_pos hx.1 (show 0 < 1 - x by linarith)]
