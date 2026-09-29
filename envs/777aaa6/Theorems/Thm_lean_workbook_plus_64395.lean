-- Prove2me | Theorems.Thm_lean_workbook_plus_64395
-- name    : lean_workbook_plus_64395
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/5766b438-eac1-4304-8799-03801670e275
-- statement:
--   Find the roots of the equation: $(x-20)(x+15) = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64395 (x : ℝ) : (x-20)*(x+15) = 0 ↔ x = 20 ∨ x = -15   :=  by sorry
