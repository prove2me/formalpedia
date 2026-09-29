-- Prove2me | Theorems.Thm_lean_workbook_plus_6081
-- name    : lean_workbook_plus_6081
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/250b254b-3b59-44a6-8f2b-698754c05465
-- statement:
--   Just expanding $ (x-2)(x-4)(x-6) = 0 $ implies that $ \boxed{x^{3}-12x^{2}+44x-48=0} $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6081 (x : ℝ) : (x-2)*(x-4)*(x-6) = 0 ↔ x^3 - 12*x^2 + 44*x - 48 = 0   :=  by sorry
