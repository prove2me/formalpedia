-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_24379
-- name    : WorkbookCorrected.plus_24379
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:35:13.239981+00:00
-- url     : https://prove2.me/theorems/5ab367b2-0594-4019-aa7f-e745b7b31acd
-- title:
--   Exact limit of a second-order averaging recurrence
-- statement:
--   Let x₁ = 3, x₂ = −7, and xₙ₊₂ = (xₙ + xₙ₊₁)/2 for every integer n ≥ 1. The limit of xₙ is −11/3.
--
--   Formalization Note: Restores the source’s initial indices and states the exact limit requested, with a complete epsilon definition of convergence.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_24379 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_24379; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_24379 (x : ℕ → ℝ) (h1 : x 1 = 3) (h2 : x 2 = -7)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+2) = (x n+x (n+1))/2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |x n - (-11/3)| < ε := by sorry
