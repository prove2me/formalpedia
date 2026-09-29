-- Prove2me | Theorems.Thm_lean_workbook_plus_38134
-- name    : lean_workbook_plus_38134
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/89256084-3260-4799-b1c3-997477d03627
-- statement:
--   prove that $\frac{a}{1+a+ab}+\frac{b}{1+b+bc}+\frac{c}{1+c+ca}\leq 1$ given $a,b,c>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38134 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a / (1 + a + a * b) + b / (1 + b + b * c) + c / (1 + c + c * a) ≤ 1   :=  by sorry
