-- Prove2me | Theorems.Thm_lean_workbook_plus_66701
-- name    : lean_workbook_plus_66701
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/6a68416c-6e14-42e6-9239-c5620d0834d6
-- statement:
--   $ \frac{x}{y} = \frac{2}{5}$ means that $ {x} = \frac{2y}{5}$ and plugging into $ y = 162 - 2x$ we get $ y = 162 - \frac{4y}{5}$ . When you solve for $ y$ , you get $ \frac{9y}{5} = 162$ . Multiply both sides by $ \frac{5}{9}$ and you get $ y = 90$ . Plugging into the original equation you get $ \frac{x}{90} = \frac{2}{5}$ when you solve for $ x$ by cross multiplying and dividing by $ 5$ yields $ x = 5$ . So, $ y = \boxed{90}$ and $ x = \boxed{36}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66701  (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x / y = 2 / 5)
  (h₂ : y = 162 - 2 * x) :
  x = 36 ∧ y = 90   :=  by sorry
