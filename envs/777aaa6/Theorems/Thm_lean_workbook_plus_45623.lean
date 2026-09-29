-- Prove2me | Theorems.Thm_lean_workbook_plus_45623
-- name    : lean_workbook_plus_45623
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/4d93f5a9-54f5-44f2-a084-a990812f3296
-- statement:
--   Prove $ \left(1-\frac{x}{n}\right)^{n}\le e^{-x}$ for $ 0\le x\le n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45623 (x : ℝ) (n : ℕ) (hn : 0 < n) (hx : 0 ≤ x ∧ x ≤ n) :
  (1 - x / n)^n ≤ exp (- x)   :=  by sorry
