-- Prove2me | Theorems.Thm_lean_workbook_plus_1166
-- name    : lean_workbook_plus_1166
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/7d085517-fbed-46d2-8fde-604976cf088f
-- statement:
--   2.nd case $b=c=1$ : \n $\frac{(a+2)^3}{27a} \ge \frac{1}{4}+\frac{(a+2)(2a+1)}{12a}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1166 (a : ℝ) (ha : 0 < a) : (a + 2) ^ 3 / (27 * a) ≥ 1 / 4 + (a + 2) * (2 * a + 1) / (12 * a)   :=  by sorry
