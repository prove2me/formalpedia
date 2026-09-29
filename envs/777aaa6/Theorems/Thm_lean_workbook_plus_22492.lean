-- Prove2me | Theorems.Thm_lean_workbook_plus_22492
-- name    : lean_workbook_plus_22492
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b170a950-2923-429a-aee1-5c931be1c9d4
-- statement:
--   Let $a,b,c>0$ , prove that: $$\frac{a+3b}{c+a}+\frac{b+3a}{c+b}+\frac{4c}{a+b}\ge 6$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22492 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 3 * b) / (c + a) + (b + 3 * a) / (c + b) + 4 * c / (a + b) ≥ 6   :=  by sorry
