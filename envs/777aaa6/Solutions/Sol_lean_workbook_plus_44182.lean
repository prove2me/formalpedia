-- Prove2me | solution 1 for lean_workbook_plus_44182
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:41.616415+00:00
-- url     : https://prove2.me/submissions/45c52d9d-d491-40f2-9aa0-fc1a711ace37

import Mathlib
set_option autoImplicit false

theorem solution (p a : ℕ) : a + 1 ≡ 0 [ZMOD p] ↔ p ∣ a + 1   := by
  rw [Int.modEq_zero_iff_dvd]
  simpa only [Int.natCast_add, Int.natCast_one] using
    (Int.natCast_dvd_natCast : (p : ℤ) ∣ ((a + 1 : ℕ) : ℤ) ↔ p ∣ a + 1)

#print axioms solution
