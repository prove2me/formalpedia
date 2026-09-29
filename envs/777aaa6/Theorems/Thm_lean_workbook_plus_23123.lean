-- Prove2me | Theorems.Thm_lean_workbook_plus_23123
-- name    : lean_workbook_plus_23123
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/8769e211-7584-42bc-b1ea-277857904ffe
-- statement:
--   Given the function $F(a,b,c,d,e,f) = (a+b+c+d+e+f)^2 - 3(a(b+c)+b(c+d)+c(d+e)+d(e+f)+e(f+a)+f(a+b))$, show that $F = \frac{1}{4}(2f-a-b+2c-d-e)^2 + \frac{3}{4}(e-d+b-a)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23123 b c d e f : ℝ) : (a + b + c + d + e + f) ^ 2 - 3 * (a * (b + c) + b * (c + d) + c * (d + e) + d * (e + f) + e * (f + a) + f * (a + b)) = 1 / 4 * (2 * f - a - b + 2 * c - d - e) ^ 2 + 3 / 4 * (e - d + b - a) ^ 2   :=  by sorry
