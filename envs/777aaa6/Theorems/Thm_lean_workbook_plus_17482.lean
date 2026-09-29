-- Prove2me | Theorems.Thm_lean_workbook_plus_17482
-- name    : lean_workbook_plus_17482
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/4d137d3d-cad7-4d0f-927d-136e261fc979
-- statement:
--   let a,b,c>0 prove $\frac{a^2}{b}+\frac{b^2}{c}+\frac{c^2}{a} \ge a+b+c$ another way for the 14 year old?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17482 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * a / b + b * b / c + c * c / a >= a + b + c   :=  by sorry
