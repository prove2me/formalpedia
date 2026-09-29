-- Prove2me | Theorems.Thm_lean_workbook_plus_50763
-- name    : lean_workbook_plus_50763
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/49679dd7-a711-4b88-acab-be79567a7853
-- statement:
--   Prove that if $x_1\geq x_2\geq x_3;y_1\leq y_2\leq y_3 $ then $(x_1+x_2+x_3)(y_1+y_2+y_3)\geq 3(x_1y_1+x_2y_2+x_3y_3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50763 (x y : ℝ) (hx: x₁ ≥ x₂ ∧ x₂ ≥ x₃) (hy: y₁ ≤ y₂ ∧ y₂ ≤ y₃) : (x₁ + x₂ + x₃) * (y₁ + y₂ + y₃) ≥ 3 * (x₁ * y₁ + x₂ * y₂ + x₃ * y₃)   :=  by sorry
