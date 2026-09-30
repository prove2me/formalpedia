-- Prove2me | solution 1 for lean_workbook_plus_53571
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:25:10.262446+00:00
-- url     : https://prove2.me/submissions/29a8ef09-5d9d-4206-a3db-07e0ac22382d

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (m n : ℕ) : (m * n + m + n) % 6 = 4 → 12 ∣ m * n := by
  intro h
  have hcases : (6 ∣ m ∧ 2 ∣ n) ∨ (2 ∣ m ∧ 6 ∣ n) := by
    have hm : m % 6 < 6 := Nat.mod_lt m (by decide)
    have hn : n % 6 < 6 := Nat.mod_lt n (by decide)
    interval_cases hm6 : m % 6 <;> interval_cases hn6 : n % 6 <;>
      norm_num [Nat.add_mod, Nat.mul_mod, hm6, hn6] at h <;> omega
  rcases hcases with ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ | ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ <;>
    exact ⟨a * b, by ring⟩

#print axioms solution
