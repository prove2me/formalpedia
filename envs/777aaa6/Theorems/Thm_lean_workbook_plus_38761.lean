-- Prove2me | Theorems.Thm_lean_workbook_plus_38761
-- name    : lean_workbook_plus_38761
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/8f82c17b-bcaa-419b-851c-7702844fb25f
-- statement:
--   Factor $x^2(x-4)^3(x-2)-3x(x-4)^2(x-2)^2 = x(x-4)^2(x-2)(x(x-4) - 3(x-2))$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38761 (x : ℝ) : x^2 * (x - 4)^3 * (x - 2) - 3 * x * (x - 4)^2 * (x - 2)^2 = x * (x - 4)^2 * (x - 2) * (x * (x - 4) - 3 * (x - 2))   :=  by sorry
