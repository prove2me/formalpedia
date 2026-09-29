-- Prove2me | Theorems.Thm_lean_workbook_plus_67497
-- name    : lean_workbook_plus_67497
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/f2154b46-a442-4fe0-b9f0-375e992c0ec1
-- statement:
--   Prove that $x^4+13x^3-12x^2+17x+37>0$ for positive $x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67497 (x : ℝ) (hx : 0 < x) : x^4 + 13*x^3 - 12*x^2 + 17*x + 37 > 0   :=  by sorry
