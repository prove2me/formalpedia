-- Prove2me | Theorems.Thm_lean_workbook_plus_48595
-- name    : lean_workbook_plus_48595
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/4b58fffa-ece3-4d31-bc6c-18920a5a8761
-- statement:
--   Given the system of equations: \n$$\begin{cases}3x+4y = 4 \\ 2x+6y = 9\end{cases}$$ Find the value of $10x + 20y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48595 (x y : ℝ) (h₁ : 3*x + 4*y = 4) (h₂ : 2*x + 6*y = 9) : 10*x + 20*y = 26   :=  by sorry
