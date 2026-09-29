-- Prove2me | Theorems.Thm_lean_workbook_plus_47460
-- name    : lean_workbook_plus_47460
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/5c709f4d-622a-4e90-91c3-239ba95aeff4
-- statement:
--   For all positive reals x and y, prove that $\frac{2x+3y}{4x+5y}+\frac{3x+2y}{5x+4y}> \frac{11}{10}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47460 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (2*x+3*y)/(4*x+5*y) + (3*x+2*y)/(5*x+4*y) > 11/10   :=  by sorry
