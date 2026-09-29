-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_25846
-- name    : WorkbookCorrected.plus_25846
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:38:45.711964+00:00
-- url     : https://prove2.me/theorems/e76c4a11-df6b-4c49-b4ac-ad8b52dc7b70
-- title:
--   Exact limit of reciprocal iteration
-- statement:
--   Let x₁ = 1 and xₙ₊₁ = 1/(1+xₙ) for every integer n ≥ 1. Then xₙ converges to (√5−1)/2.
--
--   Formalization Note: Restores the source’s initial index and supplies the exact requested limit with the full epsilon definition of convergence.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_25846 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_25846; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_25846 (x : ℕ → ℝ) (h1 : x 1 = 1)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+1) = 1/(1+x n)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |x n - (Real.sqrt 5-1)/2| < ε := by sorry
