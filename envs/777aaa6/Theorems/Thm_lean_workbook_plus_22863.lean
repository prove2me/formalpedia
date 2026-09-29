-- Prove2me | Theorems.Thm_lean_workbook_plus_22863
-- name    : lean_workbook_plus_22863
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f06d8c77-9ecd-44c5-aed2-d99b3177ab1d
-- statement:
--   Let $a,b,c>0 , \frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}=2$ and $\frac{a^2}{b+c}+\frac{b^2}{c+a}+\frac{c^2}{a+b}=\frac{5}{2}.$ Prove that $$abc\leq \frac{3}{8}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22863 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) (h : (a / (b + c)) + (b / (c + a)) + (c / (a + b)) = 2) (h' : (a ^ 2 / (b + c)) + (b ^ 2 / (c + a)) + (c ^ 2 / (a + b)) = 5 / 2) : a * b * c ≤ 3 / 8   :=  by sorry
