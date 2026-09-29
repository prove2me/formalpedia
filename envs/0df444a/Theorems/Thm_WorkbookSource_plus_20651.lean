-- Prove2me | Theorems.Thm_WorkbookSource_plus_20651
-- name    : WorkbookSource.plus_20651
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:32:16.573153+00:00
-- url     : https://prove2.me/theorems/b9efc873-5511-4797-b8af-04185a9b5a51
-- title:
--   Accuracy after thirty Newton iterations for the square root of 2002
-- statement:
--   Let x₀ = 1000 and xₙ₊₁ = (xₙ + 2002/xₙ)/2 for every natural number n. Then x₃₀ < √2002 + 10⁻⁶.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_20651 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_20651; Apache-2.0

import Mathlib

theorem WorkbookSource.plus_20651 (x : ℕ → ℝ) (x0 : x 0 = 1000) (h : ∀ n, x (n + 1) = 1 / 2 * (x n + 2002 / x n)) : x 30 < 1 / (10^6) + Real.sqrt 2002   :=  by sorry
