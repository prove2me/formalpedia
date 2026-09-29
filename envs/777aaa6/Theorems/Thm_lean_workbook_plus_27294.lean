-- Prove2me | Theorems.Thm_lean_workbook_plus_27294
-- name    : lean_workbook_plus_27294
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/0c4837bc-ea8e-4ff8-8e08-d9e96cfa48ce
-- statement:
--   Derive the formula for the difference of cubes, $a^3 - b^3 = (a-b)(a^2 + ab + b^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27294 (a b : ℝ) : a^3 - b^3 = (a - b) * (a^2 + a * b + b^2)   :=  by sorry
