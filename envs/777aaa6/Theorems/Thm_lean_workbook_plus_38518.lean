-- Prove2me | Theorems.Thm_lean_workbook_plus_38518
-- name    : lean_workbook_plus_38518
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/4fac2aa1-efd7-4599-a6de-5f5a69b9c2bd
-- statement:
--   Let $f(x)$ and $g(x)$ be functions such that $f(x) = 4x + 3$ and $g(x) = \frac{x + 1}{4}$. Evaluate $g(f(g(f(42))))$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38518 (f g : ℝ → ℝ) (f_def : ∀ x, f x = 4 * x + 3) (g_def : ∀ x, g x = (x + 1) / 4) : g (f (g (f 42))) = 44   :=  by sorry
