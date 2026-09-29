-- Prove2me | Theorems.Thm_lean_workbook_plus_30135
-- name    : lean_workbook_plus_30135
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/e33071fb-610c-4512-936a-f78490e3a2c0
-- statement:
--   If the parabola $ y = ax^2 + bx + c$ passes through the points $ ( - 1, 12), (0, 5),$ and $ (2, - 3),$ the value of $ a + b + c$ is: \n\n $ \textbf{(A)}\ - 4 \qquad \textbf{(B)}\ - 2 \qquad \textbf{(C)}\ 0 \qquad \textbf{(D)}\ 1 \qquad \textbf{(E)}\ 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30135  (a b c : ℝ)
  (h₀ : a * (-1)^2 + b * (-1) + c = 12)
  (h₁ : a * 0^2 + b * 0 + c = 5)
  (h₂ : a * 2^2 + b * 2 + c = -3) :
  a + b + c = 0   :=  by sorry
