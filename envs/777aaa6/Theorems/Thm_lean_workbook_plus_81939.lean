-- Prove2me | Theorems.Thm_lean_workbook_plus_81939
-- name    : lean_workbook_plus_81939
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/68c58b89-1678-4e4c-b096-a9859331c919
-- statement:
--   Let $ a$ and $ b$ be the two numbers so that: \n\n $ a + b = 10$ and $ ab = 20$ . \n\n The sum of the reciprocals is $ \dfrac{1}{a} + \dfrac{1}{b} = \dfrac{a + b}{ab} = \dfrac{10}{20} = \dfrac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81939  (a b : ℝ)
  (h₀ : a + b = 10)
  (h₁ : a * b = 20) :
  1 / a + 1 / b = 1 / 2   :=  by sorry
