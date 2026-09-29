-- Prove2me | Theorems.Thm_lean_workbook_plus_1392
-- name    : lean_workbook_plus_1392
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/42a8002c-2468-4bb7-9ac2-e68056b5fc0a
-- statement:
--   Find all solutions $x_1, x_2, x_3, x_4, x_5$ of the system $ x_5+x_2=yx_1 $ $ x_1+x_3=yx_2 $ $ x_2+x_4=yx_3 $ $ x_3+x_5=yx_4 $ $ x_4+x_1=yx_5 $ where $y$ is a parameter.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1392 (y : ℝ) (x : ℕ → ℝ) : (∃ x₁ x₂ x₃ x₄ x₅ : ℝ, x₅ + x₂ = y * x₁ ∧ x₁ + x₃ = y * x₂ ∧ x₂ + x₄ = y * x₃ ∧ x₃ + x₅ = y * x₄ ∧ x₄ + x₁ = y * x₅) ↔ (∃ x : ℝ, 2 * x = y)   :=  by sorry
