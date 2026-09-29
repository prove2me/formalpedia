-- Prove2me | Theorems.Thm_lean_workbook_plus_10621
-- name    : lean_workbook_plus_10621
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/c1ac4339-ddcc-4159-a879-765dc2d08e2b
-- statement:
--   D is the discriminant, or the part of the quadratic formula under the square root. The discriminant determines if a quadratic has a repeated solution, two real ones, or two complex ones. $D=b^2-4ac$. When it is plugged into $-\dfrac{D}{4a}$, you get $c-\dfrac{b^2}{4a}$, which was in NivekUil's formula for the maximum (the $y$-coordinate of the vertex).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10621  (a b c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x^2 + b * x + c)
  (h₁ : a ≠ 0) :
  -(b^2 - 4 * a * c) / (4 * a) = c - b^2 / (4 * a)   :=  by sorry
