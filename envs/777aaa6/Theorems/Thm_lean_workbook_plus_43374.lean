-- Prove2me | Theorems.Thm_lean_workbook_plus_43374
-- name    : lean_workbook_plus_43374
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/266d2ab3-ed64-4ade-84b6-e663e3806785
-- statement:
--   Prove that for any two positive reals x and y, $\frac{x^2+y^2}{x+y}\geq\frac{x+y}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43374 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x^2 + y^2) / (x + y) ≥ (x + y) / 2   :=  by sorry
