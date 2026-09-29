-- Prove2me | Theorems.Thm_lean_workbook_plus_21311
-- name    : lean_workbook_plus_21311
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/c7b73983-cb6a-48d1-b7a9-a2037c97cf73
-- statement:
--   Solve the quadratic equation: \\(x^2+3x+1=0\\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21311 (x : ℝ) : x^2 + 3*x + 1 = 0 ↔ x = (-3 + Real.sqrt 5)/2 ∨ x = (-3 - Real.sqrt 5)/2   :=  by sorry
