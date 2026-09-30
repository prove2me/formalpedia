-- Prove2me | solution 1 for lean_workbook_plus_8312
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:54:36.7586+00:00
-- url     : https://prove2.me/submissions/8b9fc8d3-f025-4cb0-8c4f-b414ac568d9b

import Mathlib
set_option autoImplicit false

theorem solution (x y z a b c : ℝ) : a = y + z ∧ b = z + x ∧ c = x + y → x = (b + c - a) / 2 ∧ y = (a + c - b) / 2 ∧ z = (a + b - c) / 2   := by
  rintro ⟨h1, h2, h3⟩
  exact ⟨by linarith, by linarith, by linarith⟩

#print axioms solution
