-- Prove2me | Theorems.Thm_lean_workbook_plus_1474
-- name    : lean_workbook_plus_1474
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/c68ed235-86ee-4520-93d5-0cebea91bbff
-- statement:
--   The sum of two nonzero real numbers is $4$ times their product. What is the sum of the reciprocals of the two numbers?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1474 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y = 4 * x * y) : x⁻¹ + y⁻¹ = 4   :=  by sorry
