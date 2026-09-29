-- Prove2me | Theorems.Thm_lean_workbook_plus_76697
-- name    : lean_workbook_plus_76697
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/94f8f3c1-4672-4f46-a61d-179d04cd358e
-- statement:
--   Calculate the sum of the series: $\sum_{r=1}^{50}\big(\frac{1}{49+r}-\frac{1}{2r(2r-1)}\big)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76697 (n : ℕ) : ∑ r in Finset.Icc 1 50, (1 / (49 + r) - 1 / (2 * r * (2 * r - 1))) = 1 / 100   :=  by sorry
