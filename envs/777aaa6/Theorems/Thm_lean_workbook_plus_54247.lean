-- Prove2me | Theorems.Thm_lean_workbook_plus_54247
-- name    : lean_workbook_plus_54247
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/d5c53165-7673-41b2-a995-c6ac8c8b982d
-- statement:
--   Find the value of $\sum_{n=1}^{50} \frac{1}{2n-1} - \frac{1}{2n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54247 : ∑ n in Finset.Icc 1 50, (1 / (2 * n - 1) - 1 / (2 * n)) = 1   :=  by sorry
