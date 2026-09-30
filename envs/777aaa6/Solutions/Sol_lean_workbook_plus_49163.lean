-- Prove2me | solution 1 for lean_workbook_plus_49163
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:44:50.271176+00:00
-- url     : https://prove2.me/submissions/7d59c0b2-2006-4069-9a09-67efdbba7aa9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (f : ℕ → ℝ) (n m : ℕ) (h₁ : m > n)
    (h₂ : f m = (2 * m + 1) / (m + 1))
    (h₃ : f n = (2 * n + 1) / (n + 1)) : f m > f n := by
  have hn : 0 < (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm : 0 < (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hnm : (n : ℝ) < m := by exact_mod_cast h₁
  rw [h₂, h₃]
  apply (div_lt_div_iff₀ hn hm).2
  nlinarith
