-- Prove2me | solution 1 for lean_workbook_plus_58459
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:22:14.57905+00:00
-- url     : https://prove2.me/submissions/99ea1de8-9dae-4b0f-b4a0-9784cdf75fa3

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

namespace DecimalIntegerNonsquare

def repunit : ℕ → ℕ
  | 0 => 0
  | n + 1 => 10 * repunit n + 1

theorem power_identity (n : ℕ) : 10 ^ n = 9 * repunit n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih, repunit]; ring

def value (n : ℕ) : ℕ := repunit n * (9 * repunit n + 3) ^ 2

theorem real_formula (n : ℕ) :
    (value n : ℝ) = ((10 : ℝ) ^ (3 * n) + 3 * 10 ^ (2 * n) - 4) / 9 := by
  have hp : (10 : ℝ) ^ n = 9 * (repunit n : ℝ) + 1 := by
    exact_mod_cast power_identity n
  have h3 : (10 : ℝ) ^ (3 * n) = ((10 : ℝ) ^ n) ^ 3 := by
    rw [← pow_mul, Nat.mul_comm]
  have h2 : (10 : ℝ) ^ (2 * n) = ((10 : ℝ) ^ n) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm]
  simp only [value, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
  rw [h3, h2, hp]
  ring

theorem block_formula (m : ℕ) :
    value (m + 2) = 16 * (5062500 * repunit m ^ 3 + 1704375 * repunit m ^ 2 +
      191250 * repunit m + 7152) + 12 := by
  simp only [value, repunit]
  ring

theorem remainder (n : ℕ) (hn : 1 < n) : value n % 16 = 12 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [block_formula]
  omega

theorem positive (n : ℕ) (hn : 1 < n) : 0 < value n := by
  have hm := remainder n hn
  omega

theorem not_square (n : ℕ) (hn : 1 < n) : ¬ IsSquare (value n) := by
  rintro ⟨k, hk⟩
  have hm : (k * k) % 16 = 12 := by rw [← hk]; exact remainder n hn
  rw [Nat.mul_mod] at hm
  have hlt : k % 16 < 16 := Nat.mod_lt _ (by decide)
  generalize k % 16 = r at hm hlt
  interval_cases r <;> norm_num at hm

theorem square_root_irrational (n : ℕ) (hn : 1 < n) :
    Irrational (Real.sqrt (((10 : ℝ) ^ (3 * n) + 3 * 10 ^ (2 * n) - 4) / 9)) := by
  rw [← real_formula n]
  exact irrational_sqrt_natCast_iff.mpr (not_square n hn)

theorem rational_value (n : ℕ) :
    ∃ q : ℚ, (q : ℝ) = ((10 : ℝ) ^ (3 * n) + 3 * 10 ^ (2 * n) - 4) / 9 := by
  refine ⟨(value n : ℚ), ?_⟩
  simpa only [Rat.cast_natCast] using real_formula n

end DecimalIntegerNonsquare

theorem solution : ¬ (∀ (n : ℕ), 1 < n →
    ¬ ∃ q : ℚ, (q : ℝ) = ((10 : ℝ) ^ (3 * n) + 3 * 10 ^ (2 * n) - 4) / 9) := by
  intro h
  exact h 2 (by decide) (DecimalIntegerNonsquare.rational_value 2)
