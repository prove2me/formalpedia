-- Prove2me | Theorems.Thm_lean_workbook_plus_41068
-- name    : lean_workbook_plus_41068
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/cfefc847-350e-4740-897b-7e8f6d726d79
-- statement:
--   For all positive integer $n\geqslant 2,$ prove that $\left(\frac{1}{2}\right)^3 \left(1+\frac{1}{3}-\frac{3}{4}\right)^{4} \left(1+\frac{1}{4}-\frac{3}{5}\right)^5\cdots \left(1+\frac{1}{n}-\frac{3}{n+1}\right)^{n+1}>\frac{2}{n^{n+1}(n+1)!}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41068 (n : ℕ) (hn : 2 ≤ n) : (1 / 2 ^ 3 * ∏ k in Finset.Icc 3 (n + 1), (1 + 1 / k - 3 / (k + 1)) ^ (k + 1)) > 2 / (n ^ (n + 1) * (n + 1)!)   :=  by sorry
