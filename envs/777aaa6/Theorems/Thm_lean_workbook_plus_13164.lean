-- Prove2me | Theorems.Thm_lean_workbook_plus_13164
-- name    : lean_workbook_plus_13164
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/c6195dac-9c78-4073-ae3a-4937919f5f93
-- statement:
--   Find all functions $f : R \to R$ such that all $x,y$ satisfy $f(x+y) = f(y)\cdot a^x$ where $a$ is a positive real number and $a \neq 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13164 (a : ℝ) (ha : a ≠ 1) (ha' : a > 0) : ∀ f : ℝ → ℝ, (∀ x y : ℝ, f (x + y) = f y * a ^ x) ↔ ∃ k :ℝ, ∀ x : ℝ, f x = k * a ^ x   :=  by sorry
