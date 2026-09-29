-- Prove2me | Theorems.Thm_lean_workbook_plus_18359
-- name    : lean_workbook_plus_18359
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/8cffd4bc-85c8-41ef-8e2f-1e215ef9bf9f
-- statement:
--   Find $f(g(h(x)))$ where $f(x) = 2x - 3$, $g(x) = \frac{1}{2}x^2 - x$, and $h(x) = x^2 + 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18359 (f g h : ℝ → ℝ) (f_def : ∀ x, f x = 2 * x - 3) (g_def : ∀ x, g x = 1 / 2 * x^2 - x) (h_def : ∀ x, h x = x^2 + 2) : ∀ x, f (g (h x)) = x^4 + 2 * x^2 - 3   :=  by sorry
