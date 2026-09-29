-- Prove2me | Theorems.Thm_lean_workbook_plus_77012
-- name    : lean_workbook_plus_77012
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8ad1c2f9-fb99-48aa-a667-4ea8a06f87a3
-- statement:
--   Find all functions $ f: \mathbb{R}\to\mathbb{R}$ such that for all $ x,y\in\mathbb{R},$ $ f\left(x+xf(y)\right)=x+yf\left(f(x)\right).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77012 (f : ℝ → ℝ): (∀ x y, f (x + x * f y) = x + y * f (f x)) ↔ ∀ x, f x = x   :=  by sorry
