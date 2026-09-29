-- Prove2me | Theorems.Thm_lean_workbook_plus_63130
-- name    : lean_workbook_plus_63130
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ccd34fb0-7d94-46d0-b0af-c5639e815441
-- statement:
--   Find the solution to this equation $x^3-13x^2+55x-75=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63130 (x : ℝ) : x^3 - 13 * x^2 + 55 * x - 75 = 0 ↔ x = 3 ∨ x = 5   :=  by sorry
