-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_43357
-- name    : WorkbookCorrected.plus_43357
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T15:06:59.777431+00:00
-- url     : https://prove2.me/theorems/11df4fe2-d10c-44db-9251-9ce662b53b23
-- title:
--   Vanishing scaled terms of an index-dependent rational recurrence
-- statement:
--   Let x₁ = 1/2 and xₙ₊₁ = n xₙ²/(1+(n+1)xₙ) for every integer n ≥ 1. Then n xₙ converges to zero.
--
--   Formalization Note: Restores the source’s positive recurrence indices; applying the original recurrence at zero contradicted the supplied initial value.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_43357 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_43357; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_43357 (x : ℕ → ℝ) (h1 : x 1=1/2)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+1)=(n:ℝ)*x n^2/(1+((n:ℝ)+1)*x n)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |(n:ℝ)*x n| < ε := by sorry
