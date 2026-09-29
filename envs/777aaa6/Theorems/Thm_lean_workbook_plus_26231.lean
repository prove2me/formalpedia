-- Prove2me | Theorems.Thm_lean_workbook_plus_26231
-- name    : lean_workbook_plus_26231
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/01de351c-dcf0-4451-b413-cf1d76260e80
-- statement:
--   Let $x,y$ be positive real number . Prove that \n $$ \frac{x}{2y+9}+\frac{ y}{3x+6}+\frac{3}{2x+3y}\geq \frac{3}{5} $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26231 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x / (2 * y + 9) + y / (3 * x + 6) + 3 / (2 * x + 3 * y)) ≥ 3 / 5   :=  by sorry
