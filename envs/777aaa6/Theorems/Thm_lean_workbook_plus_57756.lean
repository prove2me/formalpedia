-- Prove2me | Theorems.Thm_lean_workbook_plus_57756
-- name    : lean_workbook_plus_57756
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/8ff450b0-b63f-4580-a70b-5cbded4f3ec4
-- statement:
--   If $a,b,c>0$ prove that \n\n $a^5+b^5+c^5\geq abc\left(a^2+b^2+c^2+\frac{2}{3}(a-b)^2\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57756 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^5 + b^5 + c^5 ≥ a * b * c * (a^2 + b^2 + c^2 + (2 / 3) * (a - b)^2)   :=  by sorry
