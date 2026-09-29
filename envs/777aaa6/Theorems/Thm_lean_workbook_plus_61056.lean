-- Prove2me | Theorems.Thm_lean_workbook_plus_61056
-- name    : lean_workbook_plus_61056
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/e8018ae5-4f92-43c7-a026-1a0903653dbe
-- statement:
--   Alternatively, if $x<\frac{1}{10}$ then $\frac{x^2+11x+4}{3x^3+7x^2+5x+1}>3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61056 : ∀ x : ℝ, x < 1 / 10 → (x^2 + 11 * x + 4) / (3 * x^3 + 7 * x^2 + 5 * x + 1) > 3   :=  by sorry
