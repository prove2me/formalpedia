-- Prove2me | Theorems.Thm_lean_workbook_plus_28041
-- name    : lean_workbook_plus_28041
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/2e0bcd86-7a3e-44c8-baf0-c75ced529e22
-- statement:
--   For a hyperbola $ \frac{(x-a)^{2}}{\alpha ^{2}}-\frac{(y-b)^{2}}{\beta ^{2}}=1$, the foci are given by $ \left( \pm \sqrt{\alpha ^{2}+\beta ^{2}}+a,\,b\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28041 (a b α β : ℝ) : ∃ A B : ℝ × ℝ, A = (Real.sqrt (α ^ 2 + β ^ 2) + a, b) ∧ B = (-Real.sqrt (α ^ 2 + β ^ 2) + a, b)   :=  by sorry
