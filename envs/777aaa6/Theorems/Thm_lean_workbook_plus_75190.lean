-- Prove2me | Theorems.Thm_lean_workbook_plus_75190
-- name    : lean_workbook_plus_75190
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e0f137d9-ca6d-43e7-9477-903b38947f8d
-- statement:
--   Use the trigonometric identity \n $$\tan\left(\frac\pi2-x\right)=\cot x$$ to rewrite the expression.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75190 (x : ℝ) : tan (π/2 - x) = 1 / tan x   :=  by sorry
