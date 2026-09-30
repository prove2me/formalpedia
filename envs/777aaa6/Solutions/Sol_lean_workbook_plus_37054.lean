-- Prove2me | solution 1 for lean_workbook_plus_37054
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:55:52.100621+00:00
-- url     : https://prove2.me/submissions/b2a1dfd3-98b5-4fbe-83b4-954699a899e8

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

theorem solution (x : ℕ → ℝ) (n : ℕ)
    (h₀ : 0 < x (n + 1)) (h₁ : 0 < x (n + 2)) (h₂ : 0 < x n)
    (h₃ : x (n + 2) = (x n * (x (n + 1))^2) /
      (x (n + 1) + x n * (x n - 1))) :
    x (n + 1) / x (n + 2) + 1 / x (n + 1) =
      x n / x (n + 1) + 1 / x n := by
  have hd : x (n + 1) + x n * (x n - 1) ≠ 0 := by
    intro hz
    rw [hz, div_zero] at h₃
    exact (ne_of_gt h₁) h₃
  have hm := (eq_div_iff hd).1 h₃
  field_simp [ne_of_gt h₀, ne_of_gt h₁, ne_of_gt h₂]
  nlinarith only [hm]
