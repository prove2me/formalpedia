-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_53487
-- name    : WorkbookCorrected.plus_53487
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T15:19:57.040561+00:00
-- url     : https://prove2.me/theorems/273eadae-9742-4130-9b82-c29163a6139c
-- title:
--   Convergence from bounds between consecutive terms
-- statement:
--   Let a₀=a₁=1 and aₙ₊₁=aₙ−aₙ₋₁/4 for every integer n ≥ 1. The sequence converges. This proof uses inequalities between consecutive terms, without finding a closed formula.
--
--   Formalization Note: Restores the second-order recurrence’s valid indices; the original recurrence at zero contradicted the initial values.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_53487 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_53487; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_53487 (a : ℕ → ℝ) (h0 : a 0=1) (h1 : a 1=1)
    (h : ∀ n : ℕ, a (n+2)=a (n+1)-(1/4)*a n) :
    ∃ l : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n-l| < ε := by sorry
