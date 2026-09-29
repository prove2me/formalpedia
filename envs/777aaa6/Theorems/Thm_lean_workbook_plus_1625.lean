-- Prove2me | Theorems.Thm_lean_workbook_plus_1625
-- name    : lean_workbook_plus_1625
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/3045bb0e-0851-422d-851d-6a65c3335c83
-- statement:
--   Find the value of $a$ for $x = 2 + a$ where $0 < a < 1$ to solve the equation.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1625 (a : ℝ) (x : ℝ) (h₁ : 0 < a ∧ a < 1) (h₂ : x = 2 + a) : a = x - 2   :=  by sorry
