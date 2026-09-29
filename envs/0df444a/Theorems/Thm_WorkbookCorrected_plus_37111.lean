-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_37111
-- name    : WorkbookCorrected.plus_37111
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:59:10.402446+00:00
-- url     : https://prove2.me/theorems/b67d8ca8-0294-4e4e-bf51-5d7db905918a
-- title:
--   Limit of a quadratic iteration with a rational error bound
-- statement:
--   Let A₁ = 1/2 and Aₙ₊₁ = (Aₙ²+1)/2 for every integer n ≥ 1. Then Aₙ converges to 1.
--
--   Formalization Note: Restores the positive recurrence index and the complete epsilon/eventual quantifiers for convergence; the original formalization required arbitrary accuracy at a single index.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_37111 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_37111; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_37111 (a : ℕ → ℝ) (h1 : a 1=1/2)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=(a n^2+1)/2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n-1| < ε := by sorry
