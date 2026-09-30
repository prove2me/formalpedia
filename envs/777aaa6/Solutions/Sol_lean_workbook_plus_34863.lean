-- Prove2me | solution 1 for lean_workbook_plus_34863
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:19:06.88107+00:00
-- url     : https://prove2.me/submissions/7fda7736-bd18-41e2-b644-d09360563563

import Mathlib.Tactic

private lemma power_residue (n : ℕ) : 4 ^ n % 25 = 4 ^ (n % 10) % 25 := by
  conv_lhs => rw [← Nat.mod_add_div n 10]
  rw [pow_add, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

private theorem quotient_classification (n : ℕ) :
    (5 ∣ (4 ^ n + 1) / 5) ↔ 5 ∣ n := by
  have hp := power_residue n
  have hlt := Nat.mod_lt n (by decide : 0 < 10)
  simp only [Nat.dvd_iff_mod_eq_zero]
  interval_cases h : n % 10 <;> norm_num [h] at hp ⊢ <;> omega

private theorem counterfamily (k : ℕ) :
    Odd (10 * k + 1) ∧ ¬ (5 ∣ (4 ^ (10 * k + 1) + 1) / 5) := by
  constructor
  · exact ⟨5 * k, by omega⟩
  · rw [quotient_classification]
    omega

theorem solution : ¬ (∀ n : ℕ, Odd n → 5 ∣ (4 ^ n + 1) / 5) := by
  intro h
  exact (counterfamily 1).2 (h 11 (counterfamily 1).1)
