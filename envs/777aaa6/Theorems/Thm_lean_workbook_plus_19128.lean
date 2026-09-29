-- Prove2me | Theorems.Thm_lean_workbook_plus_19128
-- name    : lean_workbook_plus_19128
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/c013e0c9-a44c-46c1-adcf-2f6b11887018
-- statement:
--   Let $a,b,c>0 , \frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}=2$ and $\frac{a^2}{b+c}+\frac{b^2}{c+a}+\frac{c^2}{a+b}=5.$ Prove that $$abc\leq 3$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19128 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) (h : (a / (b + c)) + (b / (c + a)) + (c / (a + b)) = 2) (h' : (a ^ 2 / (b + c)) + (b ^ 2 / (c + a)) + (c ^ 2 / (a + b)) = 5) : a * b * c ≤ 3   :=  by sorry
