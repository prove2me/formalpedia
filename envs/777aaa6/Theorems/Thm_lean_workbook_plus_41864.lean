-- Prove2me | Theorems.Thm_lean_workbook_plus_41864
-- name    : lean_workbook_plus_41864
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/f49fd905-64df-4424-8d09-31746586df7e
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove the inequality \n $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}+\frac{3}{a+b+c}\ge \frac{4(a+b+c)}{ab+bc+ca}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41864 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / a + 1 / b + 1 / c + 3 / (a + b + c) ≥ 4 * (a + b + c) / (a * b + b * c + a * c)   :=  by sorry
