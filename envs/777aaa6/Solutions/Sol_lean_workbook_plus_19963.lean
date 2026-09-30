-- Prove2me | solution 1 for lean_workbook_plus_19963
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:15.489796+00:00
-- url     : https://prove2.me/submissions/479d9989-238c-4e14-a80c-f7885d53a5c9

import Mathlib
set_option autoImplicit false

theorem solution (k : ℕ) (h₁ : 2 ≤ k) (h₂ : 3 ^ k ≥ 2 ^ k * k) : 3 ^ (k + 1) ≥ 2 ^ (k + 1) * (k + 1)   := by
  rw [pow_succ, pow_succ]
  calc
    2 ^ k * 2 * (k + 1) = 2 ^ k * (2 * (k + 1)) := by ring
    _ ≤ 2 ^ k * (3 * k) := Nat.mul_le_mul_left (2 ^ k) (by omega)
    _ = 3 * (2 ^ k * k) := by ring
    _ ≤ 3 * 3 ^ k := Nat.mul_le_mul_left 3 h₂
    _ = 3 ^ k * 3 := by ring

#print axioms solution
