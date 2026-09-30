-- Prove2me | solution 1 for lean_workbook_plus_60981
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:02:55.60611+00:00
-- url     : https://prove2.me/submissions/2dd35987-4666-44a5-9e3f-ea01e2fc1dd6

import Mathlib.Tactic

private lemma power_residue (p : ℕ) : 10 ^ p % 13 = 10 ^ (p % 6) % 13 := by
  conv_lhs => rw [← Nat.mod_add_div p 6]
  rw [pow_add, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

private theorem residue_classification (p : ℕ) :
    (13 ∣ 10 ^ (2 * p) - 10 ^ p + 1) ↔ p % 6 = 1 ∨ p % 6 = 5 := by
  have hle : 10 ^ p ≤ 10 ^ (2 * p) :=
    pow_le_pow_right₀ (by decide) (by omega)
  have hbalance : (10 ^ (2 * p) - 10 ^ p + 1) + 10 ^ p = 10 ^ (2 * p) + 1 := by
    omega
  have h0 := power_residue p
  have h1 := power_residue (2 * p)
  have h2p : (2 * p) % 6 = (2 * (p % 6)) % 6 := by omega
  rw [h2p] at h1
  rw [Nat.dvd_iff_mod_eq_zero]
  have hlt := Nat.mod_lt p (by decide : 0 < 6)
  interval_cases h : p % 6 <;> norm_num [h] at h0 h1 ⊢ <;> omega

private theorem counterfamily (k : ℕ) :
    3 < 6 * k + 4 ∧ ¬ (13 ∣ 10 ^ (2 * (6 * k + 4)) - 10 ^ (6 * k + 4) + 1) := by
  constructor
  · omega
  · rw [residue_classification]
    omega

theorem solution : ¬ (∀ p : ℕ, p > 3 → 13 ∣ (10 ^ (2 * p) - 10 ^ p + 1)) := by
  intro h
  exact (counterfamily 0).2 (h 4 (by decide))
