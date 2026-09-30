-- Prove2me | solution 1 for lean_workbook_plus_20451
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:11.527751+00:00
-- url     : https://prove2.me/submissions/a27951e3-f56f-43ff-957e-aa183791928d

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (hab : ∀ ε : ℝ, ε > 0 → a < b + ε) : a ≤ b   := by
  by_contra h
  rw [not_le] at h
  specialize hab (a - b) (sub_pos.mpr h)
  linarith

#print axioms solution
