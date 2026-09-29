-- Prove2me | Theorems.Thm_lean_workbook_plus_79716
-- name    : lean_workbook_plus_79716
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/15ab66ce-70d5-40f5-a911-493f72c2645a
-- statement:
--   Let $x,y$ be positive real numbers such that $x+2y=8$ . Prove that $$\left(x+\dfrac{1}{y}\right)\left(y+\dfrac{1}{x}\right){\geq}4$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79716 (x y : ℝ) (hx : x > 0) (hy : y > 0) (hxy : x + 2 * y = 8) : (x + 1 / y) * (y + 1 / x) ≥ 4   :=  by sorry
