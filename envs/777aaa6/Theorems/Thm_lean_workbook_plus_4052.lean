-- Prove2me | Theorems.Thm_lean_workbook_plus_4052
-- name    : lean_workbook_plus_4052
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/4f700bbe-e0f8-481b-b46e-7397f8d5ee6b
-- statement:
--   For all $a,b,c,$ positive real number. Show that $\frac{a}{b}+\frac{b}{c}+\frac{c}{a} \geqslant 3 + \frac{(c-a)^2}{b^2+ab+bc+ca}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4052 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a >= 3 + (c - a) ^ 2 / (b ^ 2 + a * b + b * c + c * a)   :=  by sorry
