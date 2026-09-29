-- Prove2me | Theorems.Thm_lean_workbook_plus_3311
-- name    : lean_workbook_plus_3311
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/032ee41a-0d5f-44b9-b72d-d3a2d387aa60
-- statement:
--   Find the sum of the geometric series: $\frac {1}{2} + \frac{1}{2^2} + \frac{1}{2^3} + ... + \frac{1}{2^{10}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3311 (n : ℕ) : ∑ i in Finset.range n, (1/2)^i = (1 - (1/2)^n)/(1 - 1/2)   :=  by sorry
