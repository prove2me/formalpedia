-- Prove2me | Theorems.Thm_lean_workbook_plus_2037
-- name    : lean_workbook_plus_2037
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/fd5e2ebf-d5e6-4858-9af9-8f76d120a399
-- statement:
--   Given two functions f and g, $ f: \mathbb{R} \rightarrow \mathbb{R}$ and $g: \mathbb{R} \rightarrow \mathbb{R}$ , such that both f and g are decreasing functions. Proof that $ g \circ f = g(f(x)) $ also is a decreasing function.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2037 (f g : ℝ → ℝ) (hf : ∀ x y, x < y → f x > f y) (hg : ∀ x y, x < y → g x > g y) : ∀ x y, x < y → (g ∘ f) x > (g ∘ f) y   :=  by sorry
