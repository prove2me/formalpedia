-- Prove2me | Theorems.Thm_lean_workbook_plus_7539
-- name    : lean_workbook_plus_7539
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/e18fa244-99f3-4395-b6db-e2e66d5afb2c
-- statement:
--   Find integer solutions $x, y, z$ such that $xyz \neq 0$ and $x^4 + 2y^4 = z^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7539 (x y z : ℤ) (h : x * y * z ≠ 0) : x^4 + 2*y^4 = z^2 ↔ ∃ x0 y0 z0 : ℤ, x0 * y0 * z0 ≠ 0 ∧ x^4 + 2*y^4 = z^2   :=  by sorry
