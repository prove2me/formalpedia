-- Prove2me | solution 1 for lean_workbook_plus_47133
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:34.223689+00:00
-- url     : https://prove2.me/submissions/4fabf9ab-dd2b-499f-b5d6-511fa0881f97

import Mathlib
set_option autoImplicit false

theorem solution (p : ℕ) (b c x y z : ℤ) (hp : 0 < p) (h : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z) (h2 : x < p ∧ y < p ∧ z < p) (h3 : y ≡ b * x [ZMOD p]) (h4 : z ≡ c * y [ZMOD p]) : z ≡ b * c * x [ZMOD p]   := by
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h4.trans (h3.mul_left c)

#print axioms solution
