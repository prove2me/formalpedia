-- Prove2me | Theorems.Thm_lean_workbook_plus_24793
-- name    : lean_workbook_plus_24793
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/aabfd680-7d47-4eec-aa0c-27197cef5a68
-- statement:
--   $1-4(r-1)^2\geq 0\implies(r-1)^2\leq\frac{1}{4}\implies -\frac{1}{2}\leq r-1\leq\frac{1}{2}\implies\frac{1}{2}\leq r\leq\frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24793 (r : ℝ) (h : 1 - 4 * (r - 1) ^ 2 ≥ 0) : 1 / 2 ≤ r ∧ r ≤ 3 / 2   :=  by sorry
