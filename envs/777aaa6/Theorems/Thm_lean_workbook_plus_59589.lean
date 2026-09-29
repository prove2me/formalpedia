-- Prove2me | Theorems.Thm_lean_workbook_plus_59589
-- name    : lean_workbook_plus_59589
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/6627e4a8-79b5-4b7b-b8a4-4b347c4c4753
-- statement:
--   Solve the equation $-3x^2 - 3x + \frac{3}{2} = 0$ for $x$ in the interval $[-1, 1]$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59589 (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) : -3 * x ^ 2 - 3 * x + 3 / 2 = 0 ↔ x = -1 / 2 + Real.sqrt 3 / 2 ∨ x = -1 / 2 - Real.sqrt 3 / 2   :=  by sorry
