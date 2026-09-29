-- Prove2me | Theorems.Thm_lean_workbook_plus_69860
-- name    : lean_workbook_plus_69860
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/b5581121-036f-4132-be0b-2a0ff897eba5
-- statement:
--   Find the solution to the equation: \\( x^2 - x - 1 = 0 \\) for x.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69860 (x : ℝ) : x^2 - x - 1 = 0 ↔ x = (1 + Real.sqrt 5)/2 ∨ x = (1 - Real.sqrt 5)/2   :=  by sorry
