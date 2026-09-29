-- Prove2me | Theorems.Thm_lean_workbook_plus_29484
-- name    : lean_workbook_plus_29484
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/c0d13d60-d10a-4d1c-8827-30c8cde0f052
-- statement:
--   Prove that $3x^4+3x^2+5 > 9x$ for all $x \geq \frac{5}{9}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29484 (x : ℝ) (hx : 5/9 ≤ x) : 3 * x ^ 4 + 3 * x ^ 2 + 5 > 9 * x   :=  by sorry
