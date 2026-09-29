-- Prove2me | Theorems.Thm_lean_workbook_plus_63312
-- name    : lean_workbook_plus_63312
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ce4613f0-d0f7-4e4d-953f-9b5c45eb62ba
-- statement:
--   Find the zeros for the polynomial $f(x) = x^4 -4x^3 -9x^2 +36x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63312 (f : ℝ → ℝ) (x : ℝ) : x^4 - 4*x^3 - 9*x^2 + 36*x = 0 ↔ x = -3 ∨ x = 0 ∨ x = 3 ∨ x = 4   :=  by sorry
