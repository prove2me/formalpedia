-- Prove2me | solution 1 for lean_workbook_plus_45363
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:13:02.900506+00:00
-- url     : https://prove2.me/submissions/50043c14-677c-44c8-8f5a-d6eca12ea9f0

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℕ) (hgcd : Nat.gcd a b = 12) (hlcm : Nat.lcm a b = 168) : a * b = 2016   := by
  have h : a * b = 12 * 168 := by rw [← hgcd, ← hlcm, Nat.gcd_mul_lcm]
  linarith

#print axioms solution
