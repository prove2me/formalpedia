-- Prove2me | Theorems.Thm_lean_workbook_plus_33338
-- name    : lean_workbook_plus_33338
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/2043211d-d61b-4a98-a0df-e498c3003689
-- statement:
--   Solve for $x$ : $4x+3 = 12x^2 + 7x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33338 (x : ℝ) (hx : 4*x+3 = 12*x^2 + 7*x) : x = (-1 + Real.sqrt 17)/8 ∨ x = (-1 - Real.sqrt 17)/8   :=  by sorry
