-- Prove2me | Theorems.Thm_lean_workbook_plus_21296
-- name    : lean_workbook_plus_21296
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/a2a5c8de-d41c-4f5c-a78e-31ebe29b9857
-- statement:
--   Notice that: $1+\frac{2}{n^2+3n}=\frac{n^2+3n+2}{n^2+3n}=\frac{(n+1)(n+2)}{n(n+3)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21296  (n : ℝ)
  (h₀ : n ≠ 0)
  (h₁ : n + 3 ≠ 0) :
  1 + 2 / (n^2 + 3 * n) = (n + 1) * (n + 2) / (n * (n + 3))   :=  by sorry
