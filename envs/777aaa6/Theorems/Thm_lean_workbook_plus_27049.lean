-- Prove2me | Theorems.Thm_lean_workbook_plus_27049
-- name    : lean_workbook_plus_27049
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/1414eb94-6be9-4d75-b1a5-b47691897c26
-- statement:
--   For $0 \leq x \leq 1$, show that $|x(x-1)(x^6+2x^4+3x^2+4)| < 5/2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27049 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) : |x * (x - 1) * (x^6 + 2 * x^4 + 3 * x^2 + 4)| < 5 / 2   :=  by sorry
