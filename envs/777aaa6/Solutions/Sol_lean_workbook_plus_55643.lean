-- Prove2me | solution 1 for lean_workbook_plus_55643
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:46:05.145215+00:00
-- url     : https://prove2.me/submissions/c3874506-c519-4620-9e19-ef19fddf62f6

import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

theorem six_dvd_square_sub_self_iff (n : ℕ) :
    6 ∣ n ^ 2 - n ↔ n % 3 ≠ 2 := by
  have hfactor : n ^ 2 - n = n * (n - 1) := by
    simp [Nat.mul_sub_left_distrib, pow_two]
  rw [hfactor]
  constructor
  · intro h
    have h3 : 3 ∣ n * (n - 1) := dvd_trans (by decide : 3 ∣ 6) h
    rcases Nat.prime_three.dvd_mul.mp h3 with h3 | h3
    · have := Nat.mod_eq_zero_of_dvd h3
      omega
    · have := Nat.mod_eq_zero_of_dvd h3
      omega
  · intro h
    have h2 : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
    have h3 : 3 ∣ n * (n - 1) := by
      apply Nat.prime_three.dvd_mul.mpr
      simp only [Nat.dvd_iff_mod_eq_zero]
      omega
    exact (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3

theorem excluded_residue (k : ℕ) :
    ¬ 6 ∣ (3 * k + 2) ^ 2 - (3 * k + 2) := by
  rw [six_dvd_square_sub_self_iff]
  omega

theorem solution : ¬ (∀ n : ℕ, Nat.Prime n → 6 ∣ n ^ 2 - n) := by
  intro h
  exact excluded_residue 1 (h 5 (by decide))
