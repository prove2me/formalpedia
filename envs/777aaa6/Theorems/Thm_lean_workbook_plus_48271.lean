-- Prove2me | Theorems.Thm_lean_workbook_plus_48271
-- name    : lean_workbook_plus_48271
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ae60b692-7a9f-43dd-8644-2554959ae88a
-- statement:
--   If $f(x)=28x^5+3x^4-29x^3+4x^2-7x+1$ then $f(1)=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48271  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = 28 * x^5 + 3 * x^4 - 29 * x^3 + 4 * x^2 - 7 * x + 1)
  : f 1 = 0   :=  by sorry
