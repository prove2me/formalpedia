-- Prove2me | Theorems.Thm_lean_workbook_plus_27267
-- name    : lean_workbook_plus_27267
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/c376e711-0afe-4c18-bceb-b25ce0b2dd25
-- statement:
--   It's $(a-b)^2(a^2+4b^2)(a^2+2ab+2b^2)\geq0$ , which is obvious.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27267 (a b : ℝ) : (a - b) ^ 2 * (a ^ 2 + 4 * b ^ 2) * (a ^ 2 + 2 * a * b + 2 * b ^ 2) ≥ 0   :=  by sorry
