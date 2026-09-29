-- Prove2me | Theorems.Thm_lean_workbook_plus_12950
-- name    : lean_workbook_plus_12950
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/0b678559-dd4b-4996-b0e3-0ba814691722
-- statement:
--   Find the roots of the equation $x(x^2+8x+16)(4-x)=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12950 (x : ℝ) : x * (x^2 + 8 * x + 16) * (4 - x) = 0 ↔ x = 0 ∨ x = -4 ∨ x = 4   :=  by sorry
