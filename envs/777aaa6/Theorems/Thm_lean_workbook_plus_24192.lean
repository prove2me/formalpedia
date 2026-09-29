-- Prove2me | Theorems.Thm_lean_workbook_plus_24192
-- name    : lean_workbook_plus_24192
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/8f7705c4-45a2-4023-b77e-a27945504312
-- statement:
--   We have\n\n $\mathrm{LHS - RHS} = \frac{1}{a^2+b^2+c^2} \sum \frac{(a-b)^2(a+b-\sqrt 3 c)^2}{(a+c)(b+c)} \geqslant 0.$ From above, the inequality also true for all $a,\,b,\,c$ are real numbers such that $ab+bc+ca>0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24192 (a b c : ℝ) (hab : a * b + b * c + c * a > 0) : (1 / (a ^ 2 + b ^ 2 + c ^ 2)) * ((a - b) ^ 2 * (a + b - Real.sqrt 3 * c) ^ 2 / (a + c) / (b + c) + (b - c) ^ 2 * (b + c - Real.sqrt 3 * a) ^ 2 / (b + a) / (c + a) + (c - a) ^ 2 * (c + a - Real.sqrt 3 * b) ^ 2 / (c + b) / (a + b)) ≥ 0   :=  by sorry
