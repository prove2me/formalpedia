-- Prove2me | Theorems.Thm_lean_workbook_plus_80056
-- name    : lean_workbook_plus_80056
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/ae229cea-5f66-4589-a7f2-bdaa2a90497d
-- statement:
--   prove that $1-\frac{a}{1+a+ab}-\frac{b}{1+b+bc}-\frac{c}{1+c+ca}=\frac{(abc-1)^2}{(1+a+ab)(1+b+bc)(1+c+ca)}\geq0$ given $a,b,c>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80056 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 - a / (1 + a + a * b) - b / (1 + b + b * c) - c / (1 + c + c * a) : ℝ) = (a * b * c - 1) ^ 2 / ((1 + a + a * b) * (1 + b + b * c) * (1 + c + c * a))   :=  by sorry
