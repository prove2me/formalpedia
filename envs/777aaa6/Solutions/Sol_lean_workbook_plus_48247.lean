-- Prove2me | solution 1 for lean_workbook_plus_48247
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:53:33.4924+00:00
-- url     : https://prove2.me/submissions/df657ac4-fb50-4e52-805a-4d78d3f3847b

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

def lucas_normalized : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 3 * lucas_normalized (n + 1) - lucas_normalized n

theorem lucas_normalized_formula (n : ℕ) :
    (lucas_normalized n : ℝ) = ((3 + Real.sqrt 5) / 2) ^ n +
      ((3 - Real.sqrt 5) / 2) ^ n := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hr : ((3 + Real.sqrt 5) / 2) ^ 2 =
      3 * ((3 + Real.sqrt 5) / 2) - 1 := by nlinarith
  have ht : ((3 - Real.sqrt 5) / 2) ^ 2 =
      3 * ((3 - Real.sqrt 5) / 2) - 1 := by nlinarith
  induction n using Nat.twoStepInduction with
  | zero => norm_num [lucas_normalized]
  | one => simp [lucas_normalized]; ring
  | more n ih ihnext =>
    simp only [lucas_normalized, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
    rw [ih, ihnext]
    calc
      _ = ((3 + Real.sqrt 5) / 2) ^ n *
          (3 * ((3 + Real.sqrt 5) / 2) - 1) +
          ((3 - Real.sqrt 5) / 2) ^ n *
          (3 * ((3 - Real.sqrt 5) / 2) - 1) := by ring
      _ = _ := by rw [← hr, ← ht]; ring

theorem lucas_surd_integer_quotient (n : ℕ) :
    (3 + Real.sqrt 5) ^ n + (3 - Real.sqrt 5) ^ n =
      (2 : ℝ) ^ n * lucas_normalized n := by
  rw [lucas_normalized_formula, mul_add, ← mul_pow, ← mul_pow]
  congr 1 <;> congr 1 <;> ring

theorem lucas_normalized_mod_four (n : ℕ) :
    lucas_normalized n % 4 = if n % 3 = 0 then 2 else 3 := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [lucas_normalized]
  | one => norm_num [lucas_normalized]
  | more n ih ihnext =>
    rw [lucas_normalized, Int.sub_emod, Int.mul_emod, ih, ihnext]
    have hlt := Nat.mod_lt n (by decide : 0 < 3)
    interval_cases h : n % 3 <;> norm_num [Nat.add_mod, h]

def lucas_two_exponent (n : ℕ) : ℕ := n + if n % 3 = 0 then 1 else 0

theorem lucas_surd_odd_factor (n : ℕ) :
    ∃ t : ℤ, Odd t ∧
      (3 + Real.sqrt 5) ^ n + (3 - Real.sqrt 5) ^ n =
        (2 : ℝ) ^ lucas_two_exponent n * t := by
  have hm := lucas_normalized_mod_four n
  by_cases h : n % 3 = 0
  · simp only [h, if_true] at hm
    have htwo : (2 : ℤ) ∣ lucas_normalized n := by
      apply Int.dvd_of_emod_eq_zero
      omega
    obtain ⟨t, ht⟩ := htwo
    have hodd : Odd t := by
      rw [Int.odd_iff]
      omega
    refine ⟨t, hodd, ?_⟩
    rw [lucas_surd_integer_quotient, ht, Int.cast_mul, Int.cast_ofNat]
    simp only [lucas_two_exponent, h, if_true, pow_succ]
    ring
  · simp only [h, if_false] at hm
    refine ⟨lucas_normalized n, ?_, ?_⟩
    · rw [Int.odd_iff]
      omega
    · simpa only [lucas_two_exponent, h, if_false, Nat.add_zero] using
        lucas_surd_integer_quotient n

theorem lucas_surd_exact_two_divisibility (n : ℕ) :
    ∃ z : ℤ,
      (3 + Real.sqrt 5) ^ n + (3 - Real.sqrt 5) ^ n = (z : ℝ) ∧
      (2 : ℤ) ^ lucas_two_exponent n ∣ z ∧
      ¬ (2 : ℤ) ^ (lucas_two_exponent n + 1) ∣ z := by
  obtain ⟨t, ht, hs⟩ := lucas_surd_odd_factor n
  refine ⟨2 ^ lucas_two_exponent n * t, ?_, dvd_mul_right _ _, ?_⟩
  · simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using hs
  · rw [pow_succ, mul_dvd_mul_iff_left
      (pow_ne_zero (lucas_two_exponent n) (by norm_num : (2 : ℤ) ≠ 0))]
    intro h
    obtain ⟨k, hk⟩ := ht
    obtain ⟨j, hj⟩ := h
    omega

theorem solution (n : ℕ) (hn : 0 < n) (x_n : ℝ)
    (hx_n : x_n = (3 + Real.sqrt 5) ^ n + (3 - Real.sqrt 5) ^ n) :
    2 ^ n ∣ x_n := by
  refine ⟨(lucas_normalized n : ℝ), ?_⟩
  rw [hx_n, lucas_surd_integer_quotient]
