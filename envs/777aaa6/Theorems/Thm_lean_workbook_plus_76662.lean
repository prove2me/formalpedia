-- Prove2me | Theorems.Thm_lean_workbook_plus_76662
-- name    : lean_workbook_plus_76662
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/a5f75487-73af-4fc4-a0a5-a8fa02f46fee
-- statement:
--   Given $f(x) = x$ and $g(x) = 2x$, find $f(g(2))$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76662 (f g : ℕ → ℕ) (f_def : ∀ x, f x = x) (g_def : ∀ x, g x = 2 * x) : f (g 2) = 4   :=  by sorry
