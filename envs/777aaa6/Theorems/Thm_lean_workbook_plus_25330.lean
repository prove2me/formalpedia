-- Prove2me | Theorems.Thm_lean_workbook_plus_25330
-- name    : lean_workbook_plus_25330
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/2b2ef587-91d5-4292-9357-e7e34a5e1230
-- statement:
--   Prove that $(x^{n+1}+1)^2\cdot (x+1)^2 \ge 4x(x^{n+2}+1)(x^n+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25330 (x : ℝ) (n : ℕ) :
  (x^(n+1) + 1)^2 * (x + 1)^2 ≥ 4 * x * (x^(n+2) + 1) * (x^n + 1)   :=  by sorry
