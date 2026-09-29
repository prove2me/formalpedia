-- Prove2me | Theorems.Thm_lean_workbook_plus_12946
-- name    : lean_workbook_plus_12946
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/10678fd0-3008-4658-9228-83122b878bed
-- statement:
--   Find the least positive integer $n$ such that the product of the first $n$ terms of the progression $10^{1/11}, 10^{2/11}, ..., 10^{n/11}$ exceeds 100,000.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12946 (n : ℕ) : (∏ i in Finset.range n, (10:ℝ)^(i/11)) > 100000 → n >= 11   :=  by sorry
