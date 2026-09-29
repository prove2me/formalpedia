-- Prove2me | Theorems.Thm_lean_workbook_plus_74188
-- name    : lean_workbook_plus_74188
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/3d5dfc4e-fa0f-4676-9cf4-5ea658a4709d
-- statement:
--   Given $y \geq y^3+x^2+x+1$ and $x,y$ are positive reals, prove that $x^2+y^2 \geq 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74188 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : y ≥ y^3 + x^2 + x + 1) : x^2 + y^2 ≥ 1   :=  by sorry
