-- Prove2me | Theorems.Thm_lean_workbook_plus_58236
-- name    : lean_workbook_plus_58236
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/3d3c4bbe-9552-4b39-85ee-562de1d384cc
-- statement:
--   Subtract $( 3x^2 + 2xy -5y^2)$ from $6x^2-7xy+8y^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58236 (x y : ℝ) : (6 * x ^ 2 - 7 * x * y + 8 * y ^ 2) - (3 * x ^ 2 + 2 * x * y - 5 * y ^ 2) = 3 * x ^ 2 - 9 * x * y + 13 * y ^ 2   :=  by sorry
