-- Prove2me | Theorems.Thm_lean_workbook_plus_5844
-- name    : lean_workbook_plus_5844
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/28f33f25-c656-4a22-aa08-2ddb286afc2a
-- statement:
--   The percentage change between a and b is $ \frac{100(b-a)}{a}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5844 (a b : ℝ) : (b - a) / a * 100 = (100 * (b - a)) / a   :=  by sorry
