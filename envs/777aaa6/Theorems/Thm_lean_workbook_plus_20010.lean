-- Prove2me | Theorems.Thm_lean_workbook_plus_20010
-- name    : lean_workbook_plus_20010
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/953829b0-4121-4e19-96e4-8fad097feecb
-- statement:
--   $f(x)=2\cos cx$ $\forall x$ and whatever is $c\in\mathbb R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20010 (f : ℝ → ℝ) (c : ℝ) (h : ∀ x, f x = 2 * Real.cos (c * x)) : ∃ c, ∀ x, f x = 2 * Real.cos (c * x)   :=  by sorry
