-- Prove2me | Theorems.Thm_lean_workbook_plus_17061
-- name    : lean_workbook_plus_17061
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b35f39bc-0f24-4021-a461-7ee084286437
-- statement:
--   Prove that for non-negative numbers $a, b, c, d, e$, the following identity holds: \((a+b+c+d+e)(c^2+a^2+b^2+d^2+e^2) - 5abc - 5bcd - 5cde - 5ade - 5abe = (e-a)^2(2b+3/4d) + (d-e)^2(2a+3/4c) + (c-d)^2(2e+3/4b) + (b-c)^2(2d+3/4a) + (a-b)^2(2c+3/4e) + 1/4(2c-d-e)^2c + 1/4(2d-e-a)^2d + 1/4(2e-a-b)^2e + 1/4(2b-c-d)^2b + 1/4(2a-b-c)^2a\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17061 (a b c d e : ℝ) : (a+b+c+d+e)*(c^2+a^2+b^2+d^2+e^2) - 5*a*b*c - 5*b*c*d - 5*c*d*e - 5*a*d*e - 5*a*b*e = (e-a)^2*(2*b+3/4*d) + (d-e)^2*(2*a+3/4*c) + (c-d)^2*(2*e+3/4*b) + (b-c)^2*(2*d+3/4*a) + (a-b)^2*(2*c+3/4*e) + 1/4*(2*c-d-e)^2*c + 1/4*(2*d-e-a)^2*d + 1/4*(2*e-a-b)^2*e + 1/4*(2*b-c-d)^2*b + 1/4*(2*a-b-c)^2*a   :=  by sorry
