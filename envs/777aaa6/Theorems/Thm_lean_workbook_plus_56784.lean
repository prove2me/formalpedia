-- Prove2me | Theorems.Thm_lean_workbook_plus_56784
-- name    : lean_workbook_plus_56784
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/62c2c80a-17b7-42fe-a5fe-1fe851e5c790
-- statement:
--   If $x,y>0$ , prove that $4x^4+4y^4\ge x^3y+6x^2y^2+xy^3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56784 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 4*x^4 + 4*y^4 ≥ x^3*y + 6*x^2*y^2 + x*y^3   :=  by sorry
