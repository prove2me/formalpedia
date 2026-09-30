-- Prove2me | solution 1 for lean_workbook_plus_72329
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:16.075316+00:00
-- url     : https://prove2.me/submissions/0b04d7c9-362c-4ac6-b01e-156b4f0e9a1c

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (_h0 : a = 1 / 2006) (_h1 : b = 2005 / 2006) :
    a^3 + b^3 + 3 * (a * b) = (a + b) * (a^2 - a * b + b^2) + 3 * (a * b) ∧
    a^2 - a * b + b^2 + 3 * (a * b) = a^2 + 2 * a * b + b^2 ∧
    a^2 + 2 * a * b + b^2 = (a + b)^2 := by
  constructor
  · ring
  constructor <;> ring

#print axioms solution
