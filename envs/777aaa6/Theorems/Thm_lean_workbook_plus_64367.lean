-- Prove2me | Theorems.Thm_lean_workbook_plus_64367
-- name    : lean_workbook_plus_64367
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/ad338621-d937-4a60-85e3-4df7c1929aff
-- statement:
--   Given a function $f$ such that $f(x)\le x\forall x\in\mathbb{R}$ and $f(x+y)\le f(x)+f(y)\forall \{x,y\}\in\mathbb{R}$ , prove that $f(x)=x\forall x\in\mathbb{R}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64367    (f : ℝ → ℝ)
    (h₁ : ∀ x, f x ≤ x)
    (h₂ : ∀ x y, f (x + y) ≤ f x + f y) :
    ∀ x, f x = x   :=  by sorry
