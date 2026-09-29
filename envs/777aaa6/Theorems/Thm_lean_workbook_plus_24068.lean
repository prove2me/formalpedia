-- Prove2me | Theorems.Thm_lean_workbook_plus_24068
-- name    : lean_workbook_plus_24068
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/71aaf3dd-fe98-4f4d-8164-0020d7ea73cc
-- statement:
--   Find all functions $f(x)$ that satisfy $xf(x)-yf(y)=(x-y)f(x+y)$ when $f(x) = c$ for all x in R, where c is a constant
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24068 (f : ℝ → ℝ) (c : ℝ) (h₁ : ∀ x, f x = c) (h₂ : ∀ x y, x * f x - y * f y = (x - y) * f (x + y)) : ∀ x, f x = c   :=  by sorry
