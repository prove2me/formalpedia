-- Prove2me | Theorems.Thm_lean_workbook_plus_4292
-- name    : lean_workbook_plus_4292
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/0067752c-d707-433e-8ca8-82d2196d853a
-- statement:
--   For any positive numbers $a, b, c$ prove the inequalities \n $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}\ge \frac{2}{a+b}+\frac{2}{b+c}+\frac{2}{c+a}\ge \frac{9}{a+b+c}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4292 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / a + 1 / b + 1 / c) ≥ (2 / (a + b) + 2 / (b + c) + 2 / (c + a)) ∧ (2 / (a + b) + 2 / (b + c) + 2 / (c + a)) ≥ 9 / (a + b + c)   :=  by sorry
