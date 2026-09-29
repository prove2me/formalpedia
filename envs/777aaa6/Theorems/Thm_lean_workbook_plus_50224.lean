-- Prove2me | Theorems.Thm_lean_workbook_plus_50224
-- name    : lean_workbook_plus_50224
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/8ef125bc-8353-4481-93d7-315354572584
-- statement:
--   So the fraction of the distance with Ann on horseback is $\frac{17.9vt}{17.9vt+\dfrac{3124vt}{629}}=\boxed{\frac{112591}{143831}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50224  (v t : ℝ)
  (h₀ : 0 < v ∧ 0 < t)
  (h₁ : 3124 * v * t / 629 + 17.9 * v * t = 1) :
  17.9 * v * t / (17.9 * v * t + 3124 * v * t / 629) = 112591 / 143831   :=  by sorry
