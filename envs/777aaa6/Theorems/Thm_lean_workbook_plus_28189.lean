-- Prove2me | Theorems.Thm_lean_workbook_plus_28189
-- name    : lean_workbook_plus_28189
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/50ac29d3-ca8c-4f69-8490-bb8ab047349e
-- statement:
--   If $g(x)=\begin{cases}3x+21&x\ne 0\\21&x=0\end{cases}$, what's the answer and reasoning?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28189 (g : ℝ → ℝ) (g_of : ∀ x, x ≠ 0 → g x = 3 * x + 21) (g_on : g 0 = 21) : ∀ x, g x = 3 * x + 21   :=  by sorry
