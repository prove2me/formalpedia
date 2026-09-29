-- Prove2me | Theorems.Thm_lean_workbook_plus_29255
-- name    : lean_workbook_plus_29255
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/effc15c4-5698-4aff-96cf-16230805f1c0
-- statement:
--   Find the maximum value of $x_{1}.x_{2}+x_{1}.x_{3}+x_{2}.x_{3}$ given that $x_{1},x_{2},x_{3}$ are positive real numbers and $x_{1}+x_{2}+x_{3}=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29255 (x1 x2 x3 : ℝ) (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3) (hx : x1 + x2 + x3 = 1) : x1 * x2 + x1 * x3 + x2 * x3 ≤ 1 / 3   :=  by sorry
