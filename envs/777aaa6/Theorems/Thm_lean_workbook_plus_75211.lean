-- Prove2me | Theorems.Thm_lean_workbook_plus_75211
-- name    : lean_workbook_plus_75211
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/64e139b4-d531-4832-9769-c4230e569df8
-- statement:
--   Set $a_n=\frac{2n}{n^4+3n^2+4},n\in\mathbb N$ . Prove that $\frac14\le a_1+a_2+\ldots+a_n\le\frac12$ for all $n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75211 (n : ℕ) : 1 / 4 ≤ ∑ x in Finset.range n, (2 * x / (x ^ 4 + 3 * x ^ 2 + 4)) ∧ ∑ x in Finset.range n, (2 * x / (x ^ 4 + 3 * x ^ 2 + 4)) ≤ 1 / 2   :=  by sorry
