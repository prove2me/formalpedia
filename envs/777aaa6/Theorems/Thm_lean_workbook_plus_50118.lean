-- Prove2me | Theorems.Thm_lean_workbook_plus_50118
-- name    : lean_workbook_plus_50118
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/0c2516dc-8d31-4cb9-b152-4b12410a13c4
-- statement:
--   Prove that $\sum_{k=1}^{n}k = \frac{n(n+1)}{2}$ using induction
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50118 : ∀ n, ∑ k in Finset.range n, k = n * (n + 1) / 2   :=  by sorry
