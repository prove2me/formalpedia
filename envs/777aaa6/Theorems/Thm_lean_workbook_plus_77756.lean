-- Prove2me | Theorems.Thm_lean_workbook_plus_77756
-- name    : lean_workbook_plus_77756
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/59091783-317b-4912-a565-725c9eb38036
-- statement:
--   Let $ f: \mathbb{N} * \mathbb{N} \rightarrow \mathbb{N} $ defined by $ (x, y) \rightarrow \frac{(x+y)(x+y+1)}{2} + y $. Prove that $ f $ is injective.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77756 (f : ℕ × ℕ → ℕ) (x y : ℕ) (h₁ : ∀ x y : ℕ, f (x, y) = (x + y) * (x + y + 1) / 2 + y) : (x, y) = (x', y') → f (x, y) = f (x', y')   :=  by sorry
