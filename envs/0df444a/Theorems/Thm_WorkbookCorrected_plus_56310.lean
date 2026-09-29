-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_56310
-- name    : WorkbookCorrected.plus_56310
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T15:23:46.018459+00:00
-- url     : https://prove2.me/theorems/5a898390-4eed-4c67-a17b-bade9628aa30
-- title:
--   Integer terms from a consecutive-product square invariant
-- statement:
--   Let x₁=603, x₂=102, and xₙ₊₂=xₙ₊₁+xₙ+2√(xₙxₙ₊₁−2) for every integer n ≥ 1. Then every term is an integer.
--
--   Formalization Note: Restores the source’s initial indices 1 and 2 and its recurrence at positive indices.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_56310 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_56310; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_56310 (x : ℕ → ℝ) (h1 : x 1=603) (h2 : x 2=102)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+2)=x (n+1)+x n+2*Real.sqrt (x n*x (n+1)-2)) :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℤ, x n=(k:ℝ) := by sorry
