-- Prove2me | Theorems.Thm_lean_workbook_plus_65235
-- name    : lean_workbook_plus_65235
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/f706bf6f-b07a-4ece-99d1-21483accc003
-- statement:
--   $3x^4+1\geq 4x^3$ is true for all reals though. $3x^4-4x^3+1 \geq 0$ $(x-1)^2(3x^2+2x+1) \geq 0$ $(x-1)^2(3(x+\frac{1}{3})^2+\frac{2}{3})\geq 0$ . This is clearly true and only reaches equality when $x=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65235  (x : ℝ) :
  3 * x^4 + 1 ≥ 4 * x^3   :=  by sorry
