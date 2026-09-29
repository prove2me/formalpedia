-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_66762
-- name    : WorkbookCorrected.plus_66762
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T15:44:25.537967+00:00
-- url     : https://prove2.me/theorems/638fb3c1-c2f1-4d17-99b9-32ea857d0cf2
-- title:
--   A second-order reciprocal average stays between one and two
-- statement:
--   Let a₁=a₂=1 and aₙ₊₂=(aₙ₊₁+2/aₙ)/2 for every integer n≥1. Then 1≤aₙ≤2 for every integer n≥1.
--
--   Formalization Note: Uses the source’s original positive indices.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_66762 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_66762; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_66762 (a : ℕ → ℝ) (h1 : a 1 = 1) (h2 : a 2 = 1) (h : ∀ n : ℕ, 1 ≤ n → a (n+2)=(a (n+1)+2/a n)/2) : ∀ n : ℕ, 1 ≤ n → 1 ≤ a n ∧ a n ≤ 2 := by sorry
