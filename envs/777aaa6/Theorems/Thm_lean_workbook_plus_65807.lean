-- Prove2me | Theorems.Thm_lean_workbook_plus_65807
-- name    : lean_workbook_plus_65807
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/08e9add5-4d0d-4876-b12e-cd7cb31e97df
-- statement:
--   Prove $a^4/4+(a^3 b)/4+(a^3 c)/4+a^2 b c/4+(a b^3)/4+a b^2 c/4+a b c^2/4+(a c^3)/4+b^4/4+(b^3 c)/4+(b c^3)/4+c^4/4\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65807 : ∀ a b c : ℝ, a^4/4 + a^3 * b / 4 + a^3 * c / 4 + a^2 * b * c / 4 + a * b^3 / 4 + a * b^2 * c / 4 + a * b * c^2 / 4 + a * c^3 / 4 + b^4 / 4 + b^3 * c / 4 + b * c^3 / 4 + c^4 / 4 ≥ 0   :=  by sorry
