-- Prove2me | Theorems.Thm_lean_workbook_plus_2496
-- name    : lean_workbook_plus_2496
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/4ea67369-c092-442e-a2c3-cee87f814e7d
-- statement:
--   Find the polynomial function $f(x)$ such that $f(x^2+1) = (f(x))^2+1$ and $f(0) = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2496 (f : ℝ → ℝ) (hf: f (x^2+1) = (f x)^2+1 ∧ f 0 = 0) : ∃ f : ℝ → ℝ, f (x^2+1) = (f x)^2+1 ∧ f 0 = 0   :=  by sorry
