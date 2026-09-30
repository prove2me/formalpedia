-- Prove2me | solution 1 for lean_workbook_plus_20128
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:47:29.685905+00:00
-- url     : https://prove2.me/submissions/09d8bbf1-dbc3-446e-8b80-7f08628a0e9b

import Mathlib.Tactic

private theorem counterfamily (k : ℕ) :
    Even (6 * k + 2) ∧
      ¬ ((6 * k + 2) ^ 2 - 1 ∣ 3 ^ (6 * k + 2) + 5 ^ (6 * k + 2)) := by
  refine ⟨⟨3 * k + 1, by ring⟩, ?_⟩
  intro hdiv
  have hden : 3 ∣ (6 * k + 2) ^ 2 - 1 := by
    refine ⟨12 * k ^ 2 + 8 * k + 1, ?_⟩
    have hid : (6 * k + 2) ^ 2 = 3 * (12 * k ^ 2 + 8 * k + 1) + 1 := by ring
    omega
  have hnum : (3 ^ (6 * k + 2) + 5 ^ (6 * k + 2)) % 3 = 1 := by
    have he : 6 * k + 2 = 2 * (3 * k + 1) := by omega
    rw [he, pow_mul, pow_mul]
    norm_num [Nat.add_mod, Nat.pow_mod]
  have hzero := Nat.mod_eq_zero_of_dvd (hden.trans hdiv)
  omega

theorem solution : ¬ (∀ m : ℕ, Even m → m ^ 2 - 1 ∣ 3 ^ m + 5 ^ m) := by
  intro h
  exact (counterfamily 0).2 (h 2 (by decide))
