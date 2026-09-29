-- Prove2me | Theorems.Thm_lean_workbook_plus_1964
-- name    : lean_workbook_plus_1964
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/e95cf56e-12ca-4ef8-96ac-67395b5406ed
-- statement:
--   prove that \\(\\frac {a+t}{x+t}+\\frac {b+t}{y+t}+\\frac {c+t}{z+t}\\leq \\frac {a}{x}+\\frac {b}{y}+\\frac {c}{z}\\) given \\(x,y,z,a,b,c>0\\) and \\(a \geq x,b \geq y,c \geq z, t \geq 0\\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1964 (x y z a b c t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≥ x) (hbc : b ≥ y) (hca : c ≥ z) (h : t ≥ 0) : (a + t) / (x + t) + (b + t) / (y + t) + (c + t) / (z + t) ≤ a / x + b / y + c / z   :=  by sorry
