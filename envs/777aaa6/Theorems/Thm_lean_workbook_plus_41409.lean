-- Prove2me | Theorems.Thm_lean_workbook_plus_41409
-- name    : lean_workbook_plus_41409
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/89d6a9c8-1ea1-458c-b384-9e66ff2158e6
-- statement:
--   For $x,y \geq 1$ , prove that $\left( x- \frac{1}{x} \right) + \left( y - \frac{1}{y} \right) \leq \left( xy- \frac{1}{xy} \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41409 (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) : (x - 1/x) + (y - 1/y) ≤ (x*y - 1/(x*y))   :=  by sorry
