-- Prove2me | Theorems.Thm_lean_workbook_plus_58885
-- name    : lean_workbook_plus_58885
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/816f1b68-14f5-41ac-9271-57c35514f81a
-- statement:
--   Is it true that the average rate of change for a function $f(x)$ from $x_1$ to $x_2$ is the same as $\frac{y_2 - y_1}{x_2 - x_1}$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58885 (f : ℝ → ℝ) (x₁ x₂ y₁ y₂ : ℝ) (h₁ : y₁ = f x₁) (h₂ : y₂ = f x₂) : (y₂ - y₁) / (x₂ - x₁) = (f x₂ - f x₁) / (x₂ - x₁)   :=  by sorry
