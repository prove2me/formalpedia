-- Prove2me | Theorems.Thm_lean_workbook_plus_8086
-- name    : lean_workbook_plus_8086
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/bcca9da5-98dc-4852-9ced-63c342141d19
-- statement:
--   Let $a,b,c>0 $ and $\frac {(a+b- 1)^2}{c} + \frac {(b+c- 1)^2}{a} + \frac {(c + a- 1)^2}{b}=a +b+c$ . Prove that $$abc\leq 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8086 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (a + b - 1) ^ 2 / c + (b + c - 1) ^ 2 / a + (c + a - 1) ^ 2 / b = a + b + c) : a * b * c ≤ 1   :=  by sorry
