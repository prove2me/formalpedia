-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_60440
-- name    : WorkbookCorrected.plus_60440
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T15:29:32.684629+00:00
-- url     : https://prove2.me/theorems/dd0bbe06-a4e3-441c-9111-796e964d8c30
-- title:
--   An invariant interval for a rational recurrence
-- statement:
--   Let 2<a≤3, x₁=a, and xₙ₊₁=xₙ²/(2(xₙ−1)) for every integer n≥1. Then xₙ≤3 for every integer n≥1.
--
--   Formalization Note: Restores the source’s missing initial equality and its positive indices.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_60440 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_60440; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_60440 (a : ℝ) (x : ℕ → ℝ) (ha : 2 < a) (ha3 : a ≤ 3)
    (h1 : x 1=a) (h : ∀ n : ℕ, 1 ≤ n → x (n+1)=x n^2/(2*(x n-1))) :
    ∀ n : ℕ, 1 ≤ n → x n ≤ 3 := by sorry
