-- Prove2me | Theorems.Thm_lean_workbook_plus_26464
-- name    : lean_workbook_plus_26464
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/819842e2-28a1-4fc1-9f54-705145fbae7d
-- statement:
--   Given that $g(x) = x + \ln(a - x)$ with $0 < x < a - 1$, prove that $g(x)$ is increasing in the interval $(0, a - 1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26464 (a : ℝ) (x : ℝ) (hx: 0 < x ∧ x < a - 1): x + Real.log (a - x) < x + Real.log (a - x)   :=  by sorry
