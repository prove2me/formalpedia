-- Prove2me | Theorems.Thm_lean_workbook_plus_56565
-- name    : lean_workbook_plus_56565
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/da1d70cf-3ed6-4949-a8b1-f8b7449d3217
-- statement:
--   Prove that $x^5-2x^4-3x^3+12x-8\leq0$ when $3x^3-6x^2+5x-12\leq0$ and $x\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56565 : ∀ x : ℝ, (x >= 0 ∧ 3 * x ^ 3 - 6 * x ^ 2 + 5 * x - 12 <= 0) → x ^ 5 - 2 * x ^ 4 - 3 * x ^ 3 + 12 * x - 8 <= 0   :=  by sorry
