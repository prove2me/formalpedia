-- Prove2me | Theorems.Thm_lean_workbook_plus_38256
-- name    : lean_workbook_plus_38256
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/15b664f2-eb17-4267-ab19-11dc76f08191
-- statement:
--   Note that $2 * LHS = (a - b)^2 + (a - 1)^2 + (b - 1)^2 \geq 0$ holds by the Trivial Inequality. But since none of the squares can be negative, they must all equal zero, ensuring that $(a, b) = (1, 1)$ is the only solution, and $x = 0$ is hence the only (real) solution to the original equation.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38256  (x : ℝ)
  (a b : ℝ)
  (h₀ : x = a - b)
  (h₁ : x = a - 1)
  (h₂ : x = b - 1)
  (h₃ : 2 * x^2 = (a - b)^2 + (a - 1)^2 + (b - 1)^2) :
  x = 0   :=  by sorry
