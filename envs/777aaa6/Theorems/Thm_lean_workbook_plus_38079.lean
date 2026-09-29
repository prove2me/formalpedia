-- Prove2me | Theorems.Thm_lean_workbook_plus_38079
-- name    : lean_workbook_plus_38079
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/95dce11a-8d8f-4b2d-b384-18d24c6d65c5
-- statement:
--   prove Nesbitt's inequality: $\frac{a}{b+c}+\frac{b}{a+c}+\frac{c}{b+a}\geq 3/2$ for $a,b,c >0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38079 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (a + c) + c / (b + a)) ≥ 3 / 2   :=  by sorry
