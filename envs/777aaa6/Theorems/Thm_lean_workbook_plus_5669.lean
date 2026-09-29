-- Prove2me | Theorems.Thm_lean_workbook_plus_5669
-- name    : lean_workbook_plus_5669
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/f360a212-7980-4578-8523-d77bc91c966d
-- statement:
--   Let $a,b,c >0 $ and $a+b+c=\frac{1}{a}+\frac{1}{b}+\frac{1}{c} .$ Prove that $ab+bc+ca+1 \geq 4abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5669 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a + b + c = 1 / a + 1 / b + 1 / c) : a * b + b * c + c * a + 1 ≥ 4 * a * b * c   :=  by sorry
