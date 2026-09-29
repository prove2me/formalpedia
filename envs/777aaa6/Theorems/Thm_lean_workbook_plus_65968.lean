-- Prove2me | Theorems.Thm_lean_workbook_plus_65968
-- name    : lean_workbook_plus_65968
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/2ac4f870-718d-4ad7-a5db-a89b0b76ffd3
-- statement:
--   $$ 5 (x^2+ y^2) ^2 \leq 4 + (x +y) ^4\iff x^4+ y^4+x^2y^2\le 1+x^3y+ xy^3$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65968 (x y : ℝ) : 5 * (x ^ 2 + y ^ 2) ^ 2 ≤ 4 + (x + y) ^ 4 ↔ x ^ 4 + y ^ 4 + x ^ 2 * y ^ 2 ≤ 1 + x ^ 3 * y + x * y ^ 3   :=  by sorry
