-- Prove2me | Theorems.Thm_lean_workbook_plus_20137
-- name    : lean_workbook_plus_20137
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/38796454-a052-48d2-9a17-0f42420ea64a
-- statement:
--   Express the total number of ways using a summation: $\sum_{k=3}^{5}\binom{8}{k}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20137 (h : 3 ≤ 5) : ∑ k in Finset.Icc 3 5, choose 8 k = 56   :=  by sorry
