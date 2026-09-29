-- Prove2me | Theorems.Thm_lean_workbook_plus_25839
-- name    : lean_workbook_plus_25839
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/a5b0eeff-7b35-4995-a8d2-cf72f8747403
-- statement:
--   Determine the convergence of the series: $\sum^{\infty}_{n=2}\frac{1}{n(\ln(n))^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25839 : ∀ n : ℕ, n ≥ 2 → 0 < n * (Real.log n) ^ 2   :=  by sorry
