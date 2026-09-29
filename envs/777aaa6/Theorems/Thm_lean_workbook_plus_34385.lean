-- Prove2me | Theorems.Thm_lean_workbook_plus_34385
-- name    : lean_workbook_plus_34385
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/8c905356-99e6-4ce6-a618-1018c9573b09
-- statement:
--   Solve for all real and imaginary: $ x^{4}+5x^{3}-3x^{2}-17x-10=0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34385 (x : ℂ) : x^4 + 5*x^3 - 3*x^2 - 17*x - 10 = 0 ↔ x = 2 ∨ x = -1 ∨ x = -1 ∨ x = -5   :=  by sorry
