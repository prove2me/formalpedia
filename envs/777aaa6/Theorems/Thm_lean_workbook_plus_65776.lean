-- Prove2me | Theorems.Thm_lean_workbook_plus_65776
-- name    : lean_workbook_plus_65776
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/4be4e28d-5542-4ae4-9fb0-2d4497e3f88f
-- statement:
--   Calculate the minimum value of the function $f(x) = x^2+2xy+3y^2+2x+6y+4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65776 (x y : ℝ) : x^2 + 2 * x * y + 3 * y^2 + 2 * x + 6 * y + 4 ≥ 1   :=  by sorry
