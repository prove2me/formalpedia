-- Prove2me | solution 1 for lean_workbook_plus_25571
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:10:43.319888+00:00
-- url     : https://prove2.me/submissions/f8cc18fc-5d06-458e-98b5-ce7899f6a63a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b : ℝ)
    (h₁ : 0 < b ∧ b ≤ a ∧ a ≤ 4 ∧ a + b ≤ 7) : a ^ 2 + b ^ 2 ≤ 25 := by
  rcases h₁ with ⟨hb, hba, ha4, hs⟩
  by_cases hb3 : b ≤ 3
  · have ha0 : 0 ≤ a := by linarith
    have ha2 := mul_nonneg (show 0 ≤ 4 - a by linarith) (show 0 ≤ 4 + a by linarith)
    have hb2 := mul_nonneg (show 0 ≤ 3 - b by linarith) (show 0 ≤ 3 + b by linarith)
    nlinarith
  · have ha3 : 0 ≤ a - 3 := by linarith
    have hb4 : 0 ≤ 4 - b := by linarith
    have hqa := mul_nonneg ha3 (show 0 ≤ 4 - a by linarith)
    have hqb := mul_nonneg (show 0 ≤ b - 3 by linarith) hb4
    nlinarith
