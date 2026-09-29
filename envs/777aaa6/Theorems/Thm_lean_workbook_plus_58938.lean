-- Prove2me | Theorems.Thm_lean_workbook_plus_58938
-- name    : lean_workbook_plus_58938
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/f3952335-17a1-4460-816b-2fae741dcf85
-- statement:
--   Prove that $\left(x^2- \frac 12\right)^2 + \left(x - \frac 12\right)^2 >0$ for all real numbers $x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58938 (x : ℝ) : ((x^2 - 1 / 2)^2 + (x - 1 / 2)^2) > 0   :=  by sorry
