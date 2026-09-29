-- Prove2me | Theorems.Thm_lean_workbook_plus_57119
-- name    : lean_workbook_plus_57119
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/b9512564-6414-483b-a95f-2511af399189
-- statement:
--   According to Nesbitt's Inequality, where $a,b,c$ are positive reals:\n$ \frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}\ge\frac{3}{2} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57119 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 3 / 2   :=  by sorry
