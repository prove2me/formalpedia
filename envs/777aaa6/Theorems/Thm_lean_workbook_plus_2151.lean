-- Prove2me | Theorems.Thm_lean_workbook_plus_2151
-- name    : lean_workbook_plus_2151
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ac6b1101-8617-4e3a-ad4b-031c803c2a86
-- statement:
--   Prove that $f(x) = \frac{1}{cx + 1}$ for all $x > 0$ where $c \geq 0$ is a constant is a solution to the functional equation $f(x)f(yf(x)) = f(x + y)$ for all $x, y > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2151 (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℝ) (hf: ∀ x, f x = 1 / (c * x + 1)) : ∀ x y, (x > 0 ∧ y > 0) → f x * f (y * f x) = f (x + y)   :=  by sorry
