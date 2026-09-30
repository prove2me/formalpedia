-- Prove2me | solution 1 for lean_workbook_plus_70240
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:30.47067+00:00
-- url     : https://prove2.me/submissions/cc7f4055-a563-4217-877c-aa5294ba6ac2

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) :
    a * b ≤ b^2 + a * c ↔ (b - a / 2)^2 + a * (c - a / 4) ≥ 0 := by
  constructor <;> intro h <;> nlinarith [h]

#print axioms solution
