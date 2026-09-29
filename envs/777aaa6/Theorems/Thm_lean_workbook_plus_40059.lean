-- Prove2me | Theorems.Thm_lean_workbook_plus_40059
-- name    : lean_workbook_plus_40059
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/908fd7e5-778d-4b1f-8d43-921280982e18
-- statement:
--   Note that for $n > 1$, by AM-GM, $\frac{1+3+..+(2n-1)}{n} > [1.3.5....(2n-1)]^{\frac{1}{n}}$ and $\frac{2+4+....+2n}{n} > \sqrt[n]{2.4.....2n}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40059 : ∀ n ≥ 1, (∑ i in Finset.range n, (2 * i + 1)) / n > (∏ i in Finset.range n, (2 * i + 1))^(1/n) ∧  (∑ i in Finset.range n, 2 * (i + 1)) / n > (∏ i in Finset.range n, 2 * (i + 1))^(1/n)   :=  by sorry
