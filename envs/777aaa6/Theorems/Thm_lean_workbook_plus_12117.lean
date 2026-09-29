-- Prove2me | Theorems.Thm_lean_workbook_plus_12117
-- name    : lean_workbook_plus_12117
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/12451b04-79e3-40e2-b22c-dd614ab1b129
-- statement:
--   Let $a>0,b>0,a+b>1$ . \n\n $\frac{1}{a+b-1}+\frac{a}{b}+\frac{b}{a} \ge 1+\frac{1}{a}+\frac{1}{b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12117 (a b : ℝ) (ha : a > 0) (hb : b > 0) (hab : a + b > 1) : 1 / (a + b - 1) + a / b + b / a ≥ 1 + 1 / a + 1 / b   :=  by sorry
