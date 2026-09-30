-- Prove2me | solution 1 for lean_workbook_plus_60976
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:38.018894+00:00
-- url     : https://prove2.me/submissions/a19700e5-ac7c-4f82-98aa-a09512ee7489

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : ∀ n : ℕ, ¬ 17 ∣ n ^ 4 + 8 := by
  intro n hd
  have hzero := Nat.mod_eq_zero_of_dvd hd
  have hn : n % 17 < 17 := Nat.mod_lt n (by decide)
  interval_cases h : n % 17 <;>
    norm_num [Nat.add_mod, Nat.pow_mod, h] at hzero

#print axioms solution
