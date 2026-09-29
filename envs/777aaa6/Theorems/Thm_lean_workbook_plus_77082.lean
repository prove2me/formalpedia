-- Prove2me | Theorems.Thm_lean_workbook_plus_77082
-- name    : lean_workbook_plus_77082
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e4761a13-d769-4158-bbff-bb3af5a32a4e
-- statement:
--   A slightly more rigorous approach would be to start with $\frac{\sin 2x}{\cos x}$ as an expression, and not start with an equality. Transform that via the double angle identity for sine into $\frac{2\sin x \cos x}{\cos x}$ . Then, cancel the cosines (noting that we now have forced the issue of $\cos x \neq 0$ ) to get $2\sin x$ . That's your RHS.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77082  (x : ℝ)
  (h₀ : cos x ≠ 0) :
  sin (2 * x) / cos x = 2 * sin x   :=  by sorry
