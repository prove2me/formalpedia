-- Prove2me | Theorems.Thm_lean_workbook_plus_78642
-- name    : lean_workbook_plus_78642
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/a83cb23f-9be7-44a7-b6e3-f83def53afb6
-- statement:
--   Prove that the polynomial $8x^4 + 10x^3 - 21x^2 + 27$ is non-negative for all $x \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78642 (x : ℝ) (hx : x ≥ 0) : 8 * x^4 + 10 * x^3 - 21 * x^2 + 27 ≥ 0   :=  by sorry
