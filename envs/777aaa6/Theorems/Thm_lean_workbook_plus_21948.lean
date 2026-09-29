-- Prove2me | Theorems.Thm_lean_workbook_plus_21948
-- name    : lean_workbook_plus_21948
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/39c386f4-12f2-46e8-b9b5-36b62549c2a3
-- statement:
--   Function example: $f(x) = \begin{cases}e^{-\frac{1}{x}}, & x > 0 \\ 0, & x \leq 0\end{cases}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21948 (f : ℝ → ℝ) (x : ℝ) (hf: f x = if x > 0 then exp (-1/x) else 0) : f x = if x > 0 then exp (-1/x) else 0   :=  by sorry
