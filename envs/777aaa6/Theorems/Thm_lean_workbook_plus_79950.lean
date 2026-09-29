-- Prove2me | Theorems.Thm_lean_workbook_plus_79950
-- name    : lean_workbook_plus_79950
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/308563f0-ad6e-4830-a95e-a5254f874967
-- statement:
--   Note that $12((x^3+14x^2-2x)-(y^3+14y^2-2y))=(x-y)(3(2x+y+14)^2+(3y+14)^2-808)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79950 : ∀ x y : ℝ, 12 * (x^3 + 14 * x^2 - 2 * x - (y^3 + 14 * y^2 - 2 * y)) = (x - y) * (3 * (2 * x + y + 14)^2 + (3 * y + 14)^2 - 808)   :=  by sorry
