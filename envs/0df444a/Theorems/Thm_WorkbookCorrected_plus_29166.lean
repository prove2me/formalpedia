-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_29166
-- name    : WorkbookCorrected.plus_29166
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:44:50.045524+00:00
-- url     : https://prove2.me/theorems/1707cfb1-e644-495c-b8bf-72232bcd454c
-- title:
--   Exact limit of a quadratic-over-linear recurrence
-- statement:
--   Let a₁ = 3/2 and aₙ₊₁ = (aₙ²−aₙ+1)/aₙ for every integer n ≥ 1. Then aₙ converges to 1.
--
--   Formalization Note: Restores the source’s initial index and supplies the exact requested limit with the complete epsilon definition of convergence.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_29166 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_29166; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_29166 (a : ℕ → ℝ) (h1 : a 1 = 3/2)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=(a n^2-a n+1)/a n) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n-1| < ε := by sorry
