-- Prove2me | Theorems.Thm_lean_workbook_plus_50151
-- name    : lean_workbook_plus_50151
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/508851b5-ca2c-4ea6-a037-b712fd281631
-- statement:
--   Let $a,b,c>0$ and $(a+b-c)\left(\frac{1}{a}+\frac{1}{b}-\frac{1}{c}\right)=4.$ Prove that: $(a^4+b^4+c^4)\left(\frac{1}{a^4}+\frac{1}{b^4}+\frac{1}{c^4}\right)\geq 2304.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50151 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) (h : (a + b - c) * (1 / a + 1 / b - 1 / c) = 4) : (a ^ 4 + b ^ 4 + c ^ 4) * (1 / a ^ 4 + 1 / b ^ 4 + 1 / c ^ 4) ≥ 2304   :=  by sorry
