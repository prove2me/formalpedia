-- Prove2me | Theorems.Thm_lean_workbook_plus_24382
-- name    : lean_workbook_plus_24382
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/8b8fbd65-d361-496e-a79d-efe87a93c52e
-- statement:
--   Given that $$\begin{cases} a + 5b + 9c = 1 \ 4a + 2b + 3c = 2 \ 7a + 8b + 6c = 9\end{cases}$$ what is $741a + 825b + 639c$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24382 (a b c : ℝ) (h1 : a + 5*b + 9*c = 1) (h2 : 4*a + 2*b + 3*c = 2) (h3 : 7*a + 8*b + 6*c = 9) : 741*a + 825*b + 639*c = 921   :=  by sorry
