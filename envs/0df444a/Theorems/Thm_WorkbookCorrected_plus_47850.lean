-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_47850
-- name    : WorkbookCorrected.plus_47850
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T15:11:10.810483+00:00
-- url     : https://prove2.me/theorems/d09029e7-37e2-4d4d-bd14-0a3b50aa0cee
-- title:
--   Consecutive-term ratio bounds for a quadratic recurrence
-- statement:
--   Let a₁ = 1/2 and aₙ₊₁ = aₙ−aₙ² for every integer n ≥ 1. Then 1 ≤ aₙ/aₙ₊₁ ≤ 2 for every integer n ≥ 1.
--
--   Formalization Note: Restores the source’s initial index and positive recurrence indices.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_47850 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_47850; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_47850 (a : ℕ → ℝ) (h1 : a 1=1/2)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=a n-(a n)^2) :
    ∀ n : ℕ, 1 ≤ n → 1 ≤ a n/a (n+1) ∧ a n/a (n+1) ≤ 2 := by sorry
