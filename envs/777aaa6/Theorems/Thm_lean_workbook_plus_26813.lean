-- Prove2me | Theorems.Thm_lean_workbook_plus_26813
-- name    : lean_workbook_plus_26813
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/68f19628-829c-4e02-b764-c5b627a13d18
-- statement:
--   Given $\sum_{cyc} \frac {1}{1+a^2} = 2$, show that $\sum \frac{a^2}{a^2+1} = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26813 (a b c : ℝ) (h : 1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) + 1 / (1 + c ^ 2) = 2) :
  a ^ 2 / (a ^ 2 + 1) + b ^ 2 / (b ^ 2 + 1) + c ^ 2 / (c ^ 2 + 1) = 1   :=  by sorry
