-- Prove2me | Theorems.Thm_lean_workbook_plus_36390
-- name    : lean_workbook_plus_36390
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/3aac0e15-8289-40ab-915a-f51036f51159
-- statement:
--   Prove that \(abc(a+b+c) \geq a^3(b+c-a) + b^3(c+a-b) + c^3(a+b-c)\) using Schur’s Inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36390 : ∀ a b c : ℝ, a * b * c * (a + b + c) ≥ a^3 * (b + c - a) + b^3 * (c + a - b) + c^3 * (a + b - c)   :=  by sorry
