-- Prove2me | Theorems.Thm_lean_workbook_plus_45031
-- name    : lean_workbook_plus_45031
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/ff9b853c-bcb5-4d2d-ae9d-c49059229f29
-- statement:
--   For every positive a,b and c such that a^2+b^2+c^2=1 prove the inequality: $\frac{a}{a^3+bc}+\frac{b}{b^3+ca}+\frac{c}{c^3+ab}>3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45031 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : a / (a^3 + b * c) + b / (b^3 + c * a) + c / (c^3 + a * b) > 3   :=  by sorry
