-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_32724
-- name    : WorkbookCorrected.plus_32724
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:50:36.432121+00:00
-- url     : https://prove2.me/theorems/9a506d44-0367-46b9-a6bc-1dcf3c245f6f
-- title:
--   Largest-term bound from two finite-sequence moments
-- statement:
--   Let a₁ ≤ a₂ ≤ ⋯ ≤ a₁₀₀ be real numbers with sum 67 and sum of squares 45. Then a₁₀₀ ≤ 1.
--
--   Formalization Note: Restores the source’s summation indices 1 through 100, and restricts its sortedness assumption to that same finite sequence.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_32724 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_32724; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_32724 (a : ℕ → ℝ)
    (h1 : ∑ k ∈ Finset.Icc 1 100, a k = 67)
    (h2 : ∑ k ∈ Finset.Icc 1 100, (a k)^2 = 45)
    (hs : MonotoneOn a (Set.Icc 1 100)) : a 100 ≤ 1 := by sorry
