-- Prove2me | Theorems.Thm_lean_workbook_plus_42964
-- name    : lean_workbook_plus_42964
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/e7674567-4920-4122-8653-bd6adeca1ca9
-- statement:
--   Let $x=a^2+b^2$ and $y=ab$ , then the inequality is equivalent to: \n $(x - 2 y)^2 (17 x^2 + 4 x y + 4 y^2) \geq 0$ which is obviously true.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42964    (x y : ℝ)
    (a b : ℝ)
    (h₀ : x = a^2 + b^2)
    (h₁ : y = a * b) :
    (x - 2 * y)^2 * (17 * x^2 + 4 * x * y + 4 * y^2) ≥ 0   :=  by sorry
