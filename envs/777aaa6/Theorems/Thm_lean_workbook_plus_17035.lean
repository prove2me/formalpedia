-- Prove2me | Theorems.Thm_lean_workbook_plus_17035
-- name    : lean_workbook_plus_17035
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/aafa090d-7298-43f1-a3ae-687f152f7723
-- statement:
--   Solve the system of equations: $\begin{cases}x - 9y=0\\9x-y=0\end{cases}$ Find $x+y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17035 (x y : ℝ) (h₁ : x - 9*y = 0) (h₂ : 9*x - y = 0) : x + y = 0   :=  by sorry
