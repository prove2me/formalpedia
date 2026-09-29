-- Prove2me | Theorems.Thm_lean_workbook_plus_39908
-- name    : lean_workbook_plus_39908
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/9b2c7802-e188-482d-b77f-7fa81feb9b54
-- statement:
--   prove that \n $$=\frac{1}{3}-\frac{1}{5}+\frac{1}{5}-\frac{1}{7}\cdots+(-1)^{n-1} \frac{1}{2n+3} = \frac{1}{3}+(-1)^{n-1} \frac{1}{2n+3}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39908 : ∀ n, (∑ k in Finset.range n, (-1 : ℝ)^(k - 1) / (2 * k + 3)) = 1 / 3 + (-1)^(n - 1) / (2 * n + 3)   :=  by sorry
