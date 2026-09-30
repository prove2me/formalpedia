-- Prove2me | solution 1 for lean_workbook_plus_6409
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:21:42.639905+00:00
-- url     : https://prove2.me/submissions/05ff633c-1fcb-40a5-8175-8876102b941f

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : ∀ n : ℕ, 6 ∣ n * (n ^ 2 + 5) := by
  intro n
  apply Nat.dvd_of_mod_eq_zero
  have hn : n % 6 < 6 := Nat.mod_lt n (by decide)
  interval_cases h : n % 6 <;>
    norm_num [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, h]

#print axioms solution
