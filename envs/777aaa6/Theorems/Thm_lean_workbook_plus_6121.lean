-- Prove2me | Theorems.Thm_lean_workbook_plus_6121
-- name    : lean_workbook_plus_6121
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/c2221e37-a127-496b-a450-a41658af8abb
-- statement:
--   Express \\(\\sqrt{x} \\cdot \\sqrt{y}\\) in terms of exponents.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6121 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : √x * √y = x^((1:ℝ)/2) * y^((1:ℝ)/2)   :=  by sorry
