-- Prove2me | Theorems.Thm_lean_workbook_plus_775
-- name    : lean_workbook_plus_775
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/97b1ba61-9ba2-40c9-9675-82805f9f0075
-- statement:
--   Let $a, b, c > 0$. Prove that \n $$\frac{b + c}{a}+\frac{c + a}{b}+\frac{a + b} {c}\ge 2+ \frac {4(a^2+b^2+c^2)}{ab+bc+ca}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_775 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / a + (c + a) / b + (a + b) / c ≥ 2 + (4 * (a ^ 2 + b ^ 2 + c ^ 2)) / (a * b + b * c + a * c)   :=  by sorry
