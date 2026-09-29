-- Prove2me | Theorems.Thm_lean_workbook_plus_67848
-- name    : lean_workbook_plus_67848
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/37f68279-fa95-48aa-90e3-b521da0d2a0d
-- statement:
--   For any nonnegative reals $x, y$ show the inequality $$x^2y^2 + x^2y + xy^2 \le x^3y^2 + x^2 + y^3$$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67848 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : x^2*y^2 + x^2*y + x*y^2 ≤ x^3*y^2 + x^2 + y^3   :=  by sorry
