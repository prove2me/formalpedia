-- Prove2me | solution 1 for lean_workbook_plus_34837
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:19:20.572436+00:00
-- url     : https://prove2.me/submissions/61809d2e-ccbb-47b6-98c4-e84f38251be8

import Mathlib

set_option autoImplicit false

theorem solution (a b : Real) (k : Nat) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a^2 + k*b ≥ a^3 + b^2) : a^2 + b^2 ≤ k^2 + 1 := by
  have hc : 0 ≤ (a-1)^2*(2*a+1) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith [sq_nonneg (b-(k:Real))]

#print axioms solution
