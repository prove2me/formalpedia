-- Prove2me | Theorems.Thm_lean_workbook_plus_40494
-- name    : lean_workbook_plus_40494
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/756525fc-f520-4fe6-b7e5-c3a397a64c42
-- statement:
--   |$a_{n}-2|<\frac{1}{3}\left(\frac{2}{3}\right)^k$ holds for all $n\geq 3k+11$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40494 (a : ℕ → ℝ) (k : ℕ) (h₁ : 0 < k) (h₂ : ∀ n, 3 * k + 11 ≤ n → |a n - 2| < 1 / 3 * (2 / 3)^k) : ∀ n, 3 * k + 11 ≤ n → |a n - 2| < 1 / 3 * (2 / 3)^k   :=  by sorry
