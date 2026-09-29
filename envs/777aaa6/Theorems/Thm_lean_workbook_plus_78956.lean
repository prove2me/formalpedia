-- Prove2me | Theorems.Thm_lean_workbook_plus_78956
-- name    : lean_workbook_plus_78956
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e9373b9f-7827-4c8a-be1d-f5832a6e3746
-- statement:
--   Let $a,b,c>0 $ and $a(a+2b+c)=2(b^2+2c^2).$ Prove that $\frac{a}{2b+c} \geq\frac{1}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78956 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * (a + 2 * b + c) = 2 * (b ^ 2 + 2 * c ^ 2)) : (a / (2 * b + c) ≥ 1 / 3)   :=  by sorry
