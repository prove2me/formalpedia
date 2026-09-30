-- Prove2me | solution 1 for lean_workbook_plus_78439
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:02:58.667045+00:00
-- url     : https://prove2.me/submissions/1b5f9764-a57d-408e-8d9c-150deea7d0a8

import Mathlib

set_option autoImplicit false

theorem solution (d a : ℕ) (h₁ : d - a > 1) : (d - 1) * (a + 1) > d * a := by
  have hd : 1 ≤ d := by omega
  have hda : a + 1 < d := by omega
  have heq : d - 1 + 1 = d := Nat.sub_add_cancel hd
  nlinarith

#print axioms solution
