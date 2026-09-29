-- Prove2me | Theorems.Thm_lean_workbook_plus_11910
-- name    : lean_workbook_plus_11910
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/a140d303-f9b5-4c43-affd-f56b067d4c25
-- statement:
--   Prove that for $x, y, z > 0$ with $xyz = 1$, $x^2 + y^2 + z^2 \geq \frac{1}{x} + \frac{1}{y} + \frac{1}{z}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11910 (x y z : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0 ∧ x*y*z = 1) : x^2 + y^2 + z^2 >= 1/x + 1/y + 1/z   :=  by sorry
