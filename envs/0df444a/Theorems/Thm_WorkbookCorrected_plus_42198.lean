-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_42198
-- name    : WorkbookCorrected.plus_42198
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T15:04:41.669019+00:00
-- url     : https://prove2.me/theorems/d50ddf6b-05bd-494a-a8bc-f2de26b2784d
-- title:
--   Limit of a recurrence with squared reciprocal weights
-- statement:
--   Let aₙ₊₁ = (1−1/n)²aₙ+1/n for every positive integer n. Then aₙ converges to 1/2, regardless of a₁.
--
--   Formalization Note: Uses the source’s positive recurrence indices, removes an initial condition absent from the source, and identifies the exact requested limit.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_42198 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_42198; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_42198 (a : ℕ → ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=(1-1/(n:ℝ))^2*a n+1/(n:ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n-1/2| < ε := by sorry
