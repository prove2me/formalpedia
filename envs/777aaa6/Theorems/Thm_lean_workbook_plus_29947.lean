-- Prove2me | Theorems.Thm_lean_workbook_plus_29947
-- name    : lean_workbook_plus_29947
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/5ee6197f-88a5-4e62-99d7-4c1e497bcf3c
-- statement:
--   If $a, b, c>0$ prove that \n $\frac{a(b+c)^2}{2a+b+c}+\frac{b(c+a)^2}{2b+c+a}+\frac{c(a+b)^2}{2c+a+b}\le ab+bc+ca$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29947 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (b + c) ^ 2 / (2 * a + b + c) + b * (c + a) ^ 2 / (2 * b + c + a) + c * (a + b) ^ 2 / (2 * c + a + b) ≤ a * b + b * c + c * a)   :=  by sorry
