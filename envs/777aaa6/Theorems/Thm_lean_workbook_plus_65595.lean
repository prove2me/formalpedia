-- Prove2me | Theorems.Thm_lean_workbook_plus_65595
-- name    : lean_workbook_plus_65595
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/ae5db1ac-6df4-49fa-8d6e-08dfad6d9b99
-- statement:
--   $f(x)=2\cosh cx$ $\forall x$ and whatever is $c\in\mathbb R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65595 (f : ℝ → ℝ) (c : ℝ) (h : ∀ x, f x = 2 * Real.cosh (c * x)) : ∃ k : ℝ, ∀ x, f x = k * Real.cosh (c * x)   :=  by sorry
