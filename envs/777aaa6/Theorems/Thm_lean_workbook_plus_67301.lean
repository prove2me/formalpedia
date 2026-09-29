-- Prove2me | Theorems.Thm_lean_workbook_plus_67301
-- name    : lean_workbook_plus_67301
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/1c1fb06f-e252-4d28-918a-a986c8f98268
-- statement:
--   Prove that $ x^{3} + y^{3} \geq xy^{2} + x^{2}y$ for positive reals x and y
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67301 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x^3 + y^3 ≥ x * y^2 + x^2 * y   :=  by sorry
