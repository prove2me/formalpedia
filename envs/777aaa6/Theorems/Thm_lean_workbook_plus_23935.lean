-- Prove2me | Theorems.Thm_lean_workbook_plus_23935
-- name    : lean_workbook_plus_23935
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/6b24685d-1147-4e14-b997-081873e75e55
-- statement:
--   If $x_1,x_2,x_3\in\mathbb{R}$ such that $x_1+x_2+x_3=0,$ then\n$x_1x_2x_3\ge{x_1x_2+x_2x_3+x_3x_1-(x_1x_2+x_2x_3+x_3x_1)^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23935 (x₁ x₂ x₃ : ℝ) (h : x₁ + x₂ + x₃ = 0) :
  x₁ * x₂ * x₃ ≥ x₁ * x₂ + x₂ * x₃ + x₃ * x₁ - (x₁ * x₂ + x₂ * x₃ + x₃ * x₁)^2   :=  by sorry
