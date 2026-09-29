-- Prove2me | Theorems.Thm_lean_workbook_plus_6620
-- name    : lean_workbook_plus_6620
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/05b8fbae-51cb-4a1a-a6e4-4ec33be60494
-- statement:
--   Find the value of $\sum^{23}_{j=2}{(\frac{1}{j}-\frac{1}{j+1})}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6620 (h₁ : 2 ≤ 23) : ∑ j in Finset.Icc 2 23, (1 / j - 1 / (j + 1)) = 11 / 24   :=  by sorry
