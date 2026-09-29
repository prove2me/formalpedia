-- Prove2me | Theorems.Thm_lean_workbook_plus_49150
-- name    : lean_workbook_plus_49150
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/3ab76506-94ce-4a49-936f-2f542d9fac51
-- statement:
--   Factor the expression $(4a^2)^2 - (5b^2)^2$ using the difference of squares formula.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49150 (a b : ℤ) : (4 * a ^ 2) ^ 2 - (5 * b ^ 2) ^ 2 = (4 * a ^ 2 - 5 * b ^ 2) * (4 * a ^ 2 + 5 * b ^ 2)   :=  by sorry
