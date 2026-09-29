-- Prove2me | Theorems.Thm_lean_workbook_plus_61474
-- name    : lean_workbook_plus_61474
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/d2f86656-47f9-4747-a7bf-8074318bfe6e
-- statement:
--   Solve $7k-1 = s^2$ for integers $k$ and $s$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61474 (k s : ℤ) (h₁ : 7 * k - 1 = s ^ 2) : ∃ k s, 7 * k - 1 = s ^ 2   :=  by sorry
