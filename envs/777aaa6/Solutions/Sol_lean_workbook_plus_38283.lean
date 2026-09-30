-- Prove2me | solution 1 for lean_workbook_plus_38283
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:08:49.724423+00:00
-- url     : https://prove2.me/submissions/9a0747bf-6181-439b-b347-9b6a87d885f1

import Mathlib

set_option autoImplicit false

theorem solution : ∀ n : ℕ, n ≥ 0 →
    133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
  intro n _
  apply (ZMod.natCast_eq_zero_iff _ 133).mp
  push_cast
  have h12 : (12 : ZMod 133) ^ 2 = 11 := by decide
  rw [pow_add, pow_add, pow_mul, h12]
  calc
    (11 : ZMod 133) ^ n * 11 ^ 2 + 11 ^ n * 12 ^ 1 =
        11 ^ n * (11 ^ 2 + 12) := by ring
    _ = 11 ^ n * (133 : ZMod 133) := by ring
    _ = 0 := by rw [show (133 : ZMod 133) = 0 by decide, mul_zero]

#print axioms solution
