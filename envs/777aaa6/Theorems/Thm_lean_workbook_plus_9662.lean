-- Prove2me | Theorems.Thm_lean_workbook_plus_9662
-- name    : lean_workbook_plus_9662
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/41166e04-dd1d-4eff-bb44-5bc6d98200e7
-- statement:
--   Solve the equation: $7 - x^{2} = 23 - 5x^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9662 (x : ℝ) : 7 - x^2 = 23 - 5 * x^2 ↔ x = 2 ∨ x = -2   :=  by sorry
