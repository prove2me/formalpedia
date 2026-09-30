-- Prove2me | solution 1 for lean_workbook_plus_50222
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:46:04.824952+00:00
-- url     : https://prove2.me/submissions/e84dcc2b-a188-4f15-af8a-379251d8d9dd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem three_power_mod_nineteen (c : ℕ) :
    3 ^ c % 19 = 3 ^ (c % 18) % 19 := by
  calc
    3 ^ c % 19 = (3 ^ (c % 18) * (3 ^ 18) ^ (c / 18)) % 19 := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    _ = 3 ^ (c % 18) % 19 := by
      rw [Nat.mul_mod, Nat.pow_mod (3 ^ 18)]
      norm_num

theorem three_power_eight_iff (c : ℕ) :
    3 ^ c % 19 = 8 ↔ c % 18 = 3 := by
  rw [three_power_mod_nineteen]
  have hb : c % 18 < 18 := Nat.mod_lt _ (by norm_num)
  interval_cases h : c % 18 <;> norm_num

theorem solution (c : ℕ) (h₀ : 0 < c) (h₁ : 3 ^ c % 19 = 8) :
    c % 18 = 3 := by
  exact (three_power_eight_iff c).mp h₁

#print axioms solution
