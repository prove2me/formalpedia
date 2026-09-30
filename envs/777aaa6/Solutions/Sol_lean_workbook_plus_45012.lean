-- Prove2me | solution 1 for lean_workbook_plus_45012
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:33.085861+00:00
-- url     : https://prove2.me/submissions/b98b5af5-4f9c-4cfa-b3df-7bd5daccb8bf

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : x/8 + x/12 + x/6 = 2 ↔ x = 16/3   := by
  constructor <;> intro h <;> linarith

#print axioms solution
