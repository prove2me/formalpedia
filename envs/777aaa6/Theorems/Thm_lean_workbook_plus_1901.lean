-- Prove2me | Theorems.Thm_lean_workbook_plus_1901
-- name    : lean_workbook_plus_1901
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/14e4c8cf-f337-4f2d-82a8-2d17dd1dfdbd
-- statement:
--   Note that: $ a^{2}+b^{2}+c^{2}+2abc+1-2(ab+bc+ca)= (a-1)^{2}+(b-1)^{2}+(c-1)^{2}+2(a-1)(b-1)(c-1) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1901 (a b c : ℝ) : a^2 + b^2 + c^2 + 2*a*b*c + 1 - 2*(a*b + b*c + a*c) = (a-1)^2 + (b-1)^2 + (c-1)^2 + 2*(a-1)*(b-1)*(c-1)   :=  by sorry
