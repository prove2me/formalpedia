-- Prove2me | Theorems.Thm_lean_workbook_plus_68361
-- name    : lean_workbook_plus_68361
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/8b93b3a0-ae05-41b2-bc2c-42707bf7be9d
-- statement:
--   Determine the intervals of monotonicity of $f(x) = \frac{x^5 - 4x^3 + 3x}{x^2-1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68361 (f : ℝ → ℝ) (hf: f x = (x^5 - 4 * x^3 + 3 * x) / (x^2 - 1)) : ∀ x y: ℝ, x < y → (f x < f y ∨ f x = f y ∨ f x > f y)   :=  by sorry
