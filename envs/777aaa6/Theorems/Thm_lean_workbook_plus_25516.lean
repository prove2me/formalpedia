-- Prove2me | Theorems.Thm_lean_workbook_plus_25516
-- name    : lean_workbook_plus_25516
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/bf5e218d-5d94-4064-993a-2dfacfe8cdfa
-- statement:
--   Prove $4 x^6-3x^5+x^4+5x^3+2 x^2-x+1>0$ for $x > 0$ and $x \neq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25516 (x : ℝ) (hx : x > 0) (h'x : x ≠ 1) : 4 * x^6 - 3 * x^5 + x^4 + 5 * x^3 + 2 * x^2 - x + 1 > 0   :=  by sorry
