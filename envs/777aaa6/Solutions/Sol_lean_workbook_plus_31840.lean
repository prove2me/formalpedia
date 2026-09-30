-- Prove2me | solution 1 for lean_workbook_plus_31840
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:12:31.341759+00:00
-- url     : https://prove2.me/submissions/d5043ea9-0b4e-4a3b-96da-847ad301d2a6

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace SevenPowerOddSquare

theorem power_residue (x : ℕ) : 7 ^ x % 8 = 1 ∨ 7 ^ x % 8 = 7 := by
  induction x with
  | zero => simp
  | succ x hx =>
      rw [pow_succ, Nat.mul_mod]
      rcases hx with hx | hx <;> simp [hx]

theorem no_solution (x y : ℕ) : 7 ^ x - 1 ≠ 12 * (2 * y + 1) ^ 2 := by
  intro h
  have hpos : 1 ≤ 7 ^ x := one_le_pow₀ (by decide : 1 ≤ (7 : ℕ))
  have heq : 7 ^ x = 12 * (2 * y + 1) ^ 2 + 1 := by omega
  have hpoly : 12 * (2 * y + 1) ^ 2 + 1 = 8 * (6 * y * y + 6 * y + 1) + 5 := by
    ring
  rw [hpoly] at heq
  rcases power_residue x with hres | hres <;> omega

end SevenPowerOddSquare

theorem solution (x y : ℕ) (h₁ : 0 < x ∧ 0 < y)
    (h₂ : 7 ^ x - 1 = 12 * (2 * y + 1) ^ 2) : False :=
  SevenPowerOddSquare.no_solution x y h₂

#print axioms SevenPowerOddSquare.power_residue
#print axioms SevenPowerOddSquare.no_solution
#print axioms solution
