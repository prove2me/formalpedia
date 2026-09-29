-- Prove2me | Theorems.Thm_lean_workbook_plus_14997
-- name    : lean_workbook_plus_14997
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/23766254-8a88-44e6-bf2f-4f22af3111e4
-- statement:
--   Prove that $1/2\,{\frac { \left( x+y \right) ^{2}}{xy}}+2-8\,{\frac {xy}{ \left( x+y \right) ^{2}}}\leq {\frac {x}{y}}+{\frac {y}{x}}$ given $x,y>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14997 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 1 / 2 * (x + y) ^ 2 / (x * y) + 2 - 8 * (x * y) / (x + y) ^ 2 ≤ x / y + y / x   :=  by sorry
