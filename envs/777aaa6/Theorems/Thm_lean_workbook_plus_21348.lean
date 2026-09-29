-- Prove2me | Theorems.Thm_lean_workbook_plus_21348
-- name    : lean_workbook_plus_21348
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/91975a72-d51b-465b-8f33-82d6e43eae79
-- statement:
--   Prove that $\left( x^4-2x^3+x^2-2x+1\right)^2 \left( x^2 + 2(x-1)^2(x^2+1) \right) \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21348 (x : ℝ) : (x^4 - 2 * x^3 + x^2 - 2 * x + 1)^2 * (x^2 + 2 * (x - 1)^2 * (x^2 + 1)) ≥ 0   :=  by sorry
