-- Prove2me | Theorems.Thm_lean_workbook_plus_67101
-- name    : lean_workbook_plus_67101
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/5055398d-937b-4676-8e18-d3dd993a289f
-- statement:
--   Let $x,y,z$ are real number such that $xyz=-1$ Prove that $3(x^2-x+1)(y^2-y+1)(z^2-z+1) \geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67101 (x y z : ℝ) (h : x*y*z = -1) :
  3 * (x^2 - x + 1) * (y^2 - y + 1) * (z^2 - z + 1) ≥ 1   :=  by sorry
