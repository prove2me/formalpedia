-- Prove2me | Theorems.Thm_lean_workbook_plus_81748
-- name    : lean_workbook_plus_81748
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/26d4d543-ba55-43d9-8647-fc68691baf56
-- statement:
--   All the possibilities work, hence $x\in\left\{-2,-{1\over 2},1\right\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81748 {x:ℝ | x^3 + 2*x^2 - x - 2 = 0} =  {x:ℝ | x = -2 ∨ x = -1/2 ∨ x = 1}   :=  by sorry
