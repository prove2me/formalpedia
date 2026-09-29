-- Prove2me | Theorems.Thm_lean_workbook_plus_44396
-- name    : lean_workbook_plus_44396
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/269ebd40-d17a-4977-a847-a784aea97a2f
-- statement:
--   As said in the previous comments we can easily see that $f(0)=0$ and $f(x)(f(x)-x)=0$ for all $x$ . Denote: $A=\left\{ x \in R : f(x) = 0 \right\}$ and $B=\left\{ x \in R-{0} : f(y) = y \right\}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44396  (f : ℝ → ℝ)
  (h₀ : ∀ x, (x = 0 ∨ f x * (f x - x) = 0)) :
  ∀ x, (x = 0 ∨ f x = 0) ∨ f x = x   :=  by sorry
