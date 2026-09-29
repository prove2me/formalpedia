-- Prove2me | Theorems.Thm_lean_workbook_plus_21026
-- name    : lean_workbook_plus_21026
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/d725ecae-3b2f-4da3-b5d4-3f193329e05b
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that \n $$\frac{a^2}{(a+b)^2} + \frac{b^2}{(b+c)^2}+\frac{c}{c+a} \ge1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21026 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (a + b)^2 + b^2 / (b + c)^2 + c / (c + a)) ≥ 1   :=  by sorry
