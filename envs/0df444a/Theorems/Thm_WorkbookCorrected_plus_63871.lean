-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_63871
-- name    : WorkbookCorrected.plus_63871
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T15:40:10.640104+00:00
-- url     : https://prove2.me/theorems/7cdf65a1-94ed-4dea-be50-4d6850df39ae
-- title:
--   The scaled limit of an index-dependent square-root recurrence
-- statement:
--   Let x₁=1 and xₙ₊₁=√(1+nxₙ) for every integer n≥1. Then lim xₙ/n=1.
--
--   Formalization Note: Restores the source’s initial index and positive recurrence indices, and specifies the exact limit.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_63871 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_63871; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_63871 (x : ℕ → ℝ) (x1 : x 1 = 1) (h : ∀ n : ℕ, 1 ≤ n → x (n+1)=Real.sqrt (1+(n:ℝ)*x n)) : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |x n / (n:ℝ)-1| < ε := by sorry
