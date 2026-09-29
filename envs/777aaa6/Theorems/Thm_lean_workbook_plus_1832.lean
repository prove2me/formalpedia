-- Prove2me | Theorems.Thm_lean_workbook_plus_1832
-- name    : lean_workbook_plus_1832
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/dc103d87-bb84-4665-80b0-970af460969e
-- statement:
--   Solving the equation for x gives us \(x^2 - 18x + 65 = 0\), which factors to \((x-13)(x-5) = 0.\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1832 (x : ℝ) (hx : x^2 - 18*x + 65 = 0) : (x-13)*(x-5) = 0   :=  by sorry
