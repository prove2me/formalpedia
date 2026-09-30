-- Prove2me | solution 1 for lean_workbook_plus_36442
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:19:16.807298+00:00
-- url     : https://prove2.me/submissions/4201a894-bf08-4b3e-834e-fce45c731d34

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

private theorem exponent_equation (r c : ℕ) (hc : 0 < c)
    (he : 2 * r + 2 + c = 2 ^ r * (2 ^ c - 1)) : r = 1 ∧ c = 2 := by
  have hlinear (s : ℕ) : s + 1 ≤ 2 ^ s := by
    induction s with
    | zero => decide
    | succ s ih => rw [pow_succ]; omega
  have hbig (s : ℕ) (hs : 4 ≤ s) : 2 * s + 3 < 2 ^ s := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hs
    induction j with
    | zero => decide
    | succ j ih => rw [show 4 + (j + 1) = (4 + j) + 1 by omega, pow_succ]; omega
  have hbigc (s : ℕ) (hs : 4 ≤ s) : s + 9 < 2 ^ s := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hs
    induction j with
    | zero => decide
    | succ j ih => rw [show 4 + (j + 1) = (4 + j) + 1 by omega, pow_succ]; omega
  have hr : r ≤ 3 := by
    by_contra hr
    have hp := hbig r (by omega)
    have hpc : c ≤ 2 ^ c - 1 := by have := hlinear c; omega
    have hmul := Nat.mul_le_mul_left (2 ^ r) hpc
    have hstrict := Nat.mul_lt_mul_of_pos_right hp hc
    have hbase := Nat.mul_le_mul_left (2 * r + 2) (show 1 ≤ c by omega)
    nlinarith
  have hc3 : c ≤ 3 := by
    by_contra hc3
    have hp := hbigc c (by omega)
    have hpr : 1 ≤ 2 ^ r := by have := Nat.pow_pos (by decide : 0 < 2) (n := r); omega
    have hmul := Nat.mul_le_mul_right (2 ^ c - 1) hpr
    omega
  interval_cases r <;> interval_cases c <;> norm_num at he
  all_goals decide

theorem square_plus_power_two_classification (n k : ℕ) (hn : 0 < n) :
    n ^ 2 + 2 ^ n = k ^ 2 ↔ n = 6 ∧ k = 10 := by
  constructor
  · intro heq
    have hkn : n < k := by
      by_contra hk
      have hs := Nat.pow_le_pow_left (show k ≤ n by omega) 2
      have hp : 0 < 2 ^ n := Nat.pow_pos (by decide)
      omega
    have hprod : (k - n) * (k + n) = 2 ^ n := by
      have hi : (n : ℤ) ^ 2 + 2 ^ n = (k : ℤ) ^ 2 := by exact_mod_cast heq
      have hi' : ((k : ℤ) - n) * ((k : ℤ) + n) = 2 ^ n := by nlinarith
      rw [← Nat.cast_sub (Nat.le_of_lt hkn)] at hi'
      exact_mod_cast hi'
    obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show k - n ∣ 2 ^ n from ⟨k + n, hprod.symm⟩)
    obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show k + n ∣ 2 ^ n from ⟨k - n, by simpa [Nat.mul_comm] using hprod.symm⟩)
    have hab : a < b := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (by omega)
    have hnab : a + b = n := Nat.pow_right_injective (by decide : 2 ≤ 2) (by
      change 2 ^ (a + b) = 2 ^ n
      rw [pow_add, ← ha, ← hb]
      exact hprod)
    have ha0 : 0 < a := by
      by_contra ha0
      have ha' : a = 0 := by omega
      subst a
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
      rw [pow_succ] at hb
      simp only [pow_zero] at ha
      omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hab)
    have hc : 0 < c := by omega
    have hnrc : n = 2 * r + 2 + c := by omega
    change k - n = 2 ^ (r + 1) at ha
    change k + n = 2 ^ ((r + 1) + c) at hb
    have hp : 2 * n + 2 ^ (r + 1) = 2 ^ ((r + 1) + c) := by omega
    rw [pow_add 2 (r + 1) c] at hp
    simp only [pow_succ] at hp
    have he : 2 * r + 2 + c = 2 ^ r * (2 ^ c - 1) := by
      have hh : n + 2 ^ r = 2 ^ r * 2 ^ c := by nlinarith
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      omega
    obtain ⟨hr, hc⟩ := exponent_equation r c hc he
    have hn6 : n = 6 := by omega
    rw [hn6] at heq
    norm_num at heq
    exact ⟨hn6, by nlinarith⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem solution (n : ℕ) (hn : 0 < n) :
    (∃ k : ℕ, n ^ 2 + 2 ^ n = k ^ 2) ↔
      ∃ k : ℕ, n ^ 2 + 2 ^ n = k ^ 2 ∧ k > 0 := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨rfl, rfl⟩ := (square_plus_power_two_classification n k hn).mp hk
    exact ⟨10, by norm_num, by decide⟩
  · rintro ⟨k, hk, _⟩
    exact ⟨k, hk⟩
