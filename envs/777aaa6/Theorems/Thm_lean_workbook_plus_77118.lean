-- Prove2me | Theorems.Thm_lean_workbook_plus_77118
-- name    : lean_workbook_plus_77118
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/29a7656d-cc8d-47d3-998d-8e2e7cfde03b
-- statement:
--   Find all functions $f : R \to R$ such that all $x,y$ satisfy $f(x+y) = f(y)\cdot a^x$ where $a$ is a positive real number and $a \neq 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77118 (a : ℝ) (ha : a > 0 ∧ a ≠ 1) (f : ℝ → ℝ) (hf: ∀ x y : ℝ, f (x + y) = f y * a ^ x): ∃ k :ℝ, ∀ x : ℝ, f x = k * a ^ x   :=  by sorry
