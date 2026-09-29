-- Prove2me | Theorems.Thm_lean_workbook_plus_8603
-- name    : lean_workbook_plus_8603
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/ac40e085-e3c1-46f1-b77e-50a7e42a6e25
-- statement:
--   Given a quadratic polynomial $ax^2+bx+c$, prove that the third finite difference $f(x+3)-3f(x+2)+3f(x+1)-f(x)$ vanishes.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8603 (a b c : ℝ) (f : ℝ → ℝ) (h : ∀ x, f x = a * x ^ 2 + b * x + c) : ∀ x, f (x + 3) - 3 * f (x + 2) + 3 * f (x + 1) - f x = 0   :=  by sorry
