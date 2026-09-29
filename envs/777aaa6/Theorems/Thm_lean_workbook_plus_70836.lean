-- Prove2me | Theorems.Thm_lean_workbook_plus_70836
-- name    : lean_workbook_plus_70836
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/05b6dea1-9caf-4bab-8c5a-f5f8da278995
-- statement:
--   Given $ n \in{N} $ , prove that : $1^{3}+2^{3}+.....+n^{3} \le n^{4} $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70836 (n : ℕ) : ∑ i in Finset.range (n+1), i^3 ≤ n^4   :=  by sorry
