-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_34093
-- name    : WorkbookCorrected.plus_34093
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:53:32.775475+00:00
-- url     : https://prove2.me/theorems/81f14b49-11df-4cc7-976a-269dc6ce6ccf
-- title:
--   Convergence under a preceding-sum bound
-- statement:
--   Let x₁,x₂,… be positive real numbers satisfying xₙ₊₁ ≤ (x₁+⋯+xₙ)/n² for every integer n ≥ 1. Then xₙ converges to zero.
--
--   Formalization Note: Restores the source’s positive indexing and its sum of exactly the first n terms, with denominator n².
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_34093 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_34093; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_34093 (x : ℕ → ℝ) (hx : ∀ n : ℕ, 1 ≤ n → 0 < x n)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+1) ≤ (∑ i ∈ Finset.range n, x (i+1))/(n:ℝ)^2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |x n| < ε := by sorry
