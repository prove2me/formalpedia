-- Prove2me | solution 1 for lean_workbook_plus_28104
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:33:29.638393+00:00
-- url     : https://prove2.me/submissions/c8c82b0a-7529-4e07-bbaa-9159526d9bc7

import Mathlib

theorem solution : ∀ n : Nat, 19 ∣ 7 ^ (6 * n + 2) + 7 ^ (3 * n + 1) + 1 := by
  intro n
  apply (ZMod.natCast_eq_zero_iff _ 19).mp
  push_cast
  have h3 : (7 : ZMod 19) ^ 3 = 1 := by decide
  have h6 : (7 : ZMod 19) ^ 6 = 1 := by decide
  simp only [pow_add, pow_mul, h3, h6, one_pow, one_mul, pow_one]
  decide

#print axioms solution
