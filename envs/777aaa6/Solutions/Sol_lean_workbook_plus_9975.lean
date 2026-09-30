-- Prove2me | solution 1 for lean_workbook_plus_9975
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:38:00.970488+00:00
-- url     : https://prove2.me/submissions/c6c1ce21-e409-4e2d-becb-25b0ae1e0ea5

import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem quantitative_bound (k : ℕ) :
    (k + 3) ^ (k + 1) + (k + 1) * (k + 3) ^ k ≤ (k + 2) ^ (k + 2) := by
  have h := pow_add_mul_le_add_pow
    (a := (k : ℤ) + 3) (b := -1) (by omega) (by omega) (k + 1)
  have hb : 2 * ((k : ℤ) + 3) ^ k ≤ ((k : ℤ) + 2) ^ (k + 1) := by
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h
    rw [pow_succ] at h
    have he : (k : ℤ) + 3 + -1 = (k : ℤ) + 2 := by ring
    rw [he] at h
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hb (show (0 : ℤ) ≤ k + 2 by omega)
  have hc : ((k : ℤ) + 3) ^ (k + 1) + ((k : ℤ) + 1) * ((k : ℤ) + 3) ^ k ≤
      ((k : ℤ) + 2) ^ (k + 2) := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ, pow_succ]
    nlinarith
  exact_mod_cast hc

theorem strict_bound (n : ℕ) (hn : 2 ≤ n) : (n + 1) ^ (n - 1) < n ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := quantitative_bound k
  have hp : 0 < (k + 1) * (k + 3) ^ k := by positivity
  convert lt_of_lt_of_le (Nat.lt_add_of_pos_right hp) h using 1 <;>
    congr 1 <;> omega

theorem comparison_iff (n : ℕ) : (n + 1) ^ (n - 1) < n ^ n ↔ 2 ≤ n := by
  constructor
  · intro h
    by_contra hn
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;> norm_num at h
  · exact strict_bound n

theorem equality_iff (n : ℕ) : n ^ n = (n + 1) ^ (n - 1) ↔ n ≤ 1 := by
  constructor
  · intro h
    by_contra hn
    have hs := strict_bound n (by omega)
    omega
  · intro hn
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;> norm_num

theorem weak_bound (n : ℕ) : (n + 1) ^ (n - 1) ≤ n ^ n := by
  by_cases hn : 2 ≤ n
  · exact (strict_bound n hn).le
  · exact ((equality_iff n).mpr (by omega)).symm.le

theorem solution : ¬ (∀ n : ℕ, n ^ n > (n + 1) ^ (n - 1)) := by
  intro h
  have h1 := h 1
  norm_num at h1
