-- Prove2me | solution 1 for lean_workbook_plus_58901
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:57:34.033075+00:00
-- url     : https://prove2.me/submissions/a1009acd-d658-44b4-9d75-85d1bad3af6d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

set_option autoImplicit false

private theorem source_order_three_mod_seven (b : ℕ) (hb : 3 ^ b ≡ 1 [MOD 7]) : b ≡ 0 [MOD 6] := by
  have hmod : 3 ^ b % 7 = 3 ^ (b % 6) % 7 := by
    conv_lhs => rw [← Nat.mod_add_div b 6, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  change 3 ^ b % 7 = 1 % 7 at hb
  rw [hmod] at hb
  change b % 6 = 0 % 6
  have hr := Nat.mod_lt b (by decide : 0 < 6)
  interval_cases h : b % 6 <;> norm_num [h] at *

theorem solution (b : ℕ) (h₀ : b < 12) (h₁ : 3 ^ b ≡ 1 [MOD 7]) : b ≡ 0 [MOD 6] :=
  source_order_three_mod_seven b h₁
