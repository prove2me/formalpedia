-- Prove2me | solution 1 for lean_workbook_plus_61567
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:53:17.160945+00:00
-- url     : https://prove2.me/submissions/410a9d02-624b-4a14-ab69-712802dc60db

import Mathlib
set_option autoImplicit false

theorem solution {a m : ℤ} : a ≡ 1 [ZMOD m] ↔ ∃ k : ℤ, a = 1 + k * m   := by
  simpa only [mul_comm m] using
    ((Int.modEq_comm (a := a) (b := 1) (n := m)).trans
      (Int.modEq_iff_add_fac (a := 1) (b := a) (n := m)))

#print axioms solution
