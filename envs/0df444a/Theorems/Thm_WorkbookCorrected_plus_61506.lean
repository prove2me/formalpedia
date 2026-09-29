-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_61506
-- name    : WorkbookCorrected.plus_61506
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T15:35:38.067652+00:00
-- url     : https://prove2.me/theorems/d6137024-44c6-4de5-86ed-066847bb6a9a
-- title:
--   A positive square-root iteration must be constant
-- statement:
--   Let aₙ be positive real numbers satisfying aₙ₊₁=√(6−2aₙ²) for every integer n≥1. Then the sequence is constant.
--
--   Formalization Note: Restores the source’s positivity assumption and positive indices.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_61506 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_61506; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_61506 (a : ℕ → ℝ) (ha : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=Real.sqrt (6-2*(a n)^2)) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → a n=c := by sorry
