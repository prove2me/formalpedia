-- Prove2me | solution 1 for lean_workbook_plus_19714
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:17.98979+00:00
-- url     : https://prove2.me/submissions/6c17cea9-2667-4426-82e8-1c2801ff1d76

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a * b > 0) (hbc : b * c > 0) (hca : a * c > 0) : a * b + b * c + a * c > 0 ∧ 1 / (a * b) + 1 / (b * c) + 1 / (a * c) > 0   := by
  constructor <;> positivity

#print axioms solution
