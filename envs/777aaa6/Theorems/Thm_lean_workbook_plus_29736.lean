-- Prove2me | Theorems.Thm_lean_workbook_plus_29736
-- name    : lean_workbook_plus_29736
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/3130838a-b979-4c84-84e4-c3ddc1d34b40
-- statement:
--   From $(x^3-y^3)(x-y) \geq 0$ , we have $x^4+y^4 \geq xy(x^2+y^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29736 (x y : ℝ) : x^4 + y^4 ≥ x * y * (x^2 + y^2)   :=  by sorry
