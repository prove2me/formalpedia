-- Prove2me | Theorems.Thm_lean_workbook_plus_28566
-- name    : lean_workbook_plus_28566
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/dd2faf3a-7d8f-4eda-a82d-0e2ee8ad6b8a
-- statement:
--   Prove the identity $\sum_{k=1}^{n}(k+1)^{3}-k^{3}=\sum_{k=1}^{n}3k^{2}+3k+1$ and then use it to find a formula for $\sum_{k=1}^{n}k^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28566 : ∀ n, ∑ k in Finset.Icc 1 n, ((k + 1) ^ 3 - k ^ 3) = ∑ k in Finset.Icc 1 n, (3 * k ^ 2 + 3 * k + 1)   :=  by sorry
