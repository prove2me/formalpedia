-- Prove2me | Theorems.Thm_lean_workbook_plus_65765
-- name    : lean_workbook_plus_65765
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/ddf643fc-e34b-4d8d-afac-cd1da3936323
-- statement:
--   For $a, b, c>0$ prove that \n $\frac{4a+11b}{6a+13b+c}+\frac{4b+11c}{a+6b+13c}+\frac{4c+11a}{13a+b+6c}\leq\frac{9}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65765 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (4*a + 11*b) / (6*a + 13*b + c) + (4*b + 11*c) / (a + 6*b + 13*c) + (4*c + 11*a) / (13*a + b + 6*c) ≤ 9 / 4   :=  by sorry
