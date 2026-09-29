-- Prove2me | Theorems.Thm_lean_workbook_plus_81473
-- name    : lean_workbook_plus_81473
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/15d3b137-460d-424d-a703-701ec8471671
-- statement:
--   Prove that $\frac{1}{1\cdot 2} + \frac{1}{2\cdot 3} + \cdots + \frac{1}{(n+1)\cdot (n+2)} = \frac{n+1}{n+2}$ using telescoping series and mathematical induction.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81473 (n : ℕ) : ∑ k in Finset.range (n+1), (1:ℝ) / ((k + 1) * (k + 2)) = (n + 1) / (n + 2)   :=  by sorry
