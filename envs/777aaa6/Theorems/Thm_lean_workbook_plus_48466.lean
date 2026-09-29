-- Prove2me | Theorems.Thm_lean_workbook_plus_48466
-- name    : lean_workbook_plus_48466
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/79acdf7b-d150-4b8a-9e2d-d30a69436ef1
-- statement:
--   A6. Given that $a$ and $b$ are reals that satisfy the following equations, find the value of $ab$ . $\begin{cases} a^2+b^2=100\a+b=12\ \end{cases}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48466 (a b : ℝ) (h₁ : a^2 + b^2 = 100) (h₂ : a + b = 12) : a * b = 22   :=  by sorry
