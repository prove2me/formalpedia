-- Prove2me | solution 1 for lean_workbook_plus_9731
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:10:13.480327+00:00
-- url     : https://prove2.me/submissions/3848667d-51cf-4e82-9cc3-ec583a0c9b32

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto

namespace QuarticSquareValues

theorem large_square (n : ℤ) (hn : 2 < |n|) : 9 ≤ n ^ 2 := by
  have h : 3 ≤ |n| := by omega
  nlinarith [sq_abs n, sq_nonneg (|n| - 3)]

theorem consecutive_bounds (n : ℤ) (hn : 2 < |n|) :
    (2 * n ^ 2 + n - 1) ^ 2 < 4 * (n ^ 4 + n ^ 3 + 1) ∧
      4 * (n ^ 4 + n ^ 3 + 1) < (2 * n ^ 2 + n) ^ 2 := by
  have h := large_square n hn
  constructor <;> nlinarith [sq_nonneg n, sq_nonneg (n + 1)]

theorem no_large_square (n k : ℤ) (hn : 2 < |n|) :
    n ^ 4 + n ^ 3 + 1 ≠ k ^ 2 := by
  intro h
  obtain ⟨hl, hu⟩ := consecutive_bounds n hn
  have hn2 := large_square n hn
  have hs : 0 ≤ 2 * n ^ 2 + n - 1 := by nlinarith [sq_nonneg (n + 1)]
  have hk : 0 ≤ 2 * |k| := by positivity
  have he : (2 * |k|) ^ 2 = 4 * k ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  have hlo : 2 * n ^ 2 + n - 1 < 2 * |k| :=
    (sq_lt_sq₀ hs hk).mp (by nlinarith [hl, he])
  have hhi : 2 * |k| < 2 * n ^ 2 + n :=
    (sq_lt_sq₀ hk (by omega)).mp (by nlinarith [hu, he])
  omega

theorem classification (n k : ℤ) :
    n ^ 4 + n ^ 3 + 1 = k ^ 2 ↔
      (n = -2 ∧ (k = -3 ∨ k = 3)) ∨
      (n = -1 ∧ (k = -1 ∨ k = 1)) ∨
      (n = 0 ∧ (k = -1 ∨ k = 1)) ∨
      (n = 2 ∧ (k = -5 ∨ k = 5)) := by
  constructor
  · intro h
    have hn : |n| ≤ 2 := by
      by_contra hh
      exact no_large_square n k (by omega) h
    obtain ⟨hnl, hnu⟩ := abs_le.mp hn
    have hk2 : k ^ 2 ≤ 25 := by interval_cases n <;> norm_num at h ⊢ <;> omega
    have hk : -5 ≤ k ∧ k ≤ 5 := by
      constructor <;> nlinarith [sq_nonneg (k - 5), sq_nonneg (k + 5)]
    obtain ⟨hkl, hku⟩ := hk
    interval_cases n <;> interval_cases k <;> norm_num at h <;> norm_num
  · rintro (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ |
      ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩) <;> norm_num

theorem square_value_iff (n : ℤ) :
    (∃ k : ℤ, n ^ 4 + n ^ 3 + 1 = k ^ 2) ↔ n = -2 ∨ n = -1 ∨ n = 0 ∨ n = 2 := by
  constructor
  · rintro ⟨k, hk⟩
    rcases (classification n k).mp hk with h | h | h | h <;> tauto
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨3, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨5, by norm_num⟩

end QuarticSquareValues

theorem solution (n : ℤ) (hn : abs n > 2) :
    (2 * n ^ 2 + n - 2) ^ 2 < 4 * (n ^ 4 + n ^ 3 + 1) ∧
      4 * (n ^ 4 + n ^ 3 + 1) < (2 * n ^ 2 + n) ^ 2 := by
  obtain ⟨hl, hu⟩ := QuarticSquareValues.consecutive_bounds n hn
  have hn2 := QuarticSquareValues.large_square n hn
  have hs : 0 ≤ 2 * n ^ 2 + n - 2 := by nlinarith [sq_nonneg (n + 1)]
  refine ⟨lt_trans ?_ hl, hu⟩
  exact (sq_lt_sq₀ hs (by omega)).mpr (by omega)
