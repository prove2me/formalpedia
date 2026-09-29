-- Prove2me | Theorems.Thm_lean_workbook_plus_39773
-- name    : lean_workbook_plus_39773
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/c16762a5-3f6a-4e07-85e6-ed73042feb6c
-- statement:
--   If $x,y$ be be nonnegative real numbers such that $x+y^{2}\geq x^{2}+y^{3}$ , then $3x^{2}+2y^{3}\leq5$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39773 (x y : ℝ) (hx: x >= 0 ∧ y >= 0) (h : x + y^2 >= x^2 + y^3): 3 * x^2 + 2 * y^3 <= 5   :=  by sorry
