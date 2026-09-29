-- Prove2me | Theorems.Thm_lean_workbook_plus_36158
-- name    : lean_workbook_plus_36158
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/fccb959c-d22c-4d64-a3b3-b82d4fa05f96
-- statement:
--   Prove that if $a,b,c>0$ then \n $$\frac{b+c}{a}+\frac{c+a}{b}+\frac{a+b}{c}\geq \frac{4(a^2+b^2+c^2)}{ab+bc+ca}+2$$\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36158 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / a + (c + a) / b + (a + b) / c ≥ 4 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c) + 2   :=  by sorry
