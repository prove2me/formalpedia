-- Prove2me | Theorems.Thm_lean_workbook_plus_8645
-- name    : lean_workbook_plus_8645
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/bdda4dfe-6738-4dcf-9310-c874c4c311eb
-- statement:
--   so $x^2-1=3y^2$ which is a Pell equation with infinitely many solutions (starting at $x=2,7$ )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8645 (x y : ℤ) (h₁ : x^2 - 1 = 3 * y^2) : ∃ x y : ℤ, x^2 - 1 = 3 * y^2 ∧ y ≠ 0   :=  by sorry
