-- Prove2me | Theorems.Thm_lean_workbook_plus_36804
-- name    : lean_workbook_plus_36804
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/b5572294-3e88-4cf4-9881-515bf7b7393a
-- statement:
--   How does the equality $xf(y)=yf(x)$ for all $x, y \in \mathbb{R}$ imply that $f(x)=kx$ for some constant $k$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36804 (f : ℝ → ℝ) (hf : ∀ x y, x * f y = y * f x) : ∃ k, ∀ x, f x = k * x   :=  by sorry
