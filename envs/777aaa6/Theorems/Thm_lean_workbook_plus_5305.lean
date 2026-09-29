-- Prove2me | Theorems.Thm_lean_workbook_plus_5305
-- name    : lean_workbook_plus_5305
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/10514417-a6ce-4670-8181-8e244581ed78
-- statement:
--   For $n \in \mathbb{Z}$, prove that 1+(1/2)+(1/4)+(1/8)+(1/16)+...+1/2^n<2
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5305 : ∀ n, ∑ i in Finset.range n, (1/2)^i < 2   :=  by sorry
