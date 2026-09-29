-- Prove2me | Theorems.Thm_lean_workbook_plus_42255
-- name    : lean_workbook_plus_42255
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/fa2c4861-5874-46bd-8982-a0353ae57c4e
-- statement:
--   Given a function $f$ such that $f(x+y)=f(x)f(y)$ and $f(0) \neq 0$, prove that $f(-x)=\frac{1}{f(x)}$ for all real x.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42255 (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) = f x * f y) (h : f 0 ≠ 0) : ∀ x, f (-x) = 1 / f x   :=  by sorry
