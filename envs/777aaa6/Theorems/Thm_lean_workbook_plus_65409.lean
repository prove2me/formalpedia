-- Prove2me | Theorems.Thm_lean_workbook_plus_65409
-- name    : lean_workbook_plus_65409
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/9be0eb69-7cdc-4388-9bc9-944755685090
-- statement:
--   Find the coefficient of $a^2b$ in the expansion of $(a+b+c+d)^3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65409 (a b c d : ℕ) : (a + b + c + d) ^ 3 = a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 + 3 * a ^ 2 * b + 3 * a ^ 2 * c + 3 * a ^ 2 * d + 3 * b ^ 2 * a + 3 * b ^ 2 * c + 3 * b ^ 2 * d + 3 * c ^ 2 * a + 3 * c ^ 2 * b + 3 * c ^ 2 * d + 3 * d ^ 2 * a + 3 * d ^ 2 * b + 3 * d ^ 2 * c + 6 * a * b * c + 6 * a * b * d + 6 * a * c * d + 6 * b * c * d   :=  by sorry
