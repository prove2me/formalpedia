-- Prove2me | Theorems.Thm_lean_workbook_plus_76498
-- name    : lean_workbook_plus_76498
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/60b8c664-e9b4-4c72-81c3-aaf75a83dbdb
-- statement:
--   Let $f: \mathbb{R} \rightarrow \mathbb{R}$ be a function such that $f(x+y) = f(x)f(y)$ for all $x, y \in \mathbb{R}$. Show that $f(0) = 0$ or $f(0) = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76498 (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) = f x * f y) : f 0 = 0 ∨ f 0 = 1   :=  by sorry
