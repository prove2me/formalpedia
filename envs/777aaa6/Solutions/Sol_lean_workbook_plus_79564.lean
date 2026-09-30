-- Prove2me | solution 1 for lean_workbook_plus_79564
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:22:23.844451+00:00
-- url     : https://prove2.me/submissions/61f7402b-a0b8-4ae5-a851-b8c16eb50cf4

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (m : ℕ) (h₀ : 0 < m) (h₁ : Nat.Prime 521)
    (h₂ : 8 ^ 520 % 521 = 1) :
    (8 ^ (m + 520 * 521) + 9 * (m + 520 * 521) ^ 2) % 521 =
      (8 ^ m + 9 * m ^ 2) % 521 := by
  rw [pow_add, pow_mul]
  norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h₂]

#print axioms solution
