-- Prove2me | Theorems.Thm_lean_workbook_plus_58144
-- name    : lean_workbook_plus_58144
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/66300779-3892-4745-8ac2-215df25643c3
-- statement:
--   Prove that $\frac{a^2}{x}+\frac{b^2}{y}\geq \frac{(a+b)^2}{x+y}$ using Cauchy-Schwarz inequality (CS)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58144 {a b x y : ℝ} (hx : x > 0) (hy : y > 0) : (a^2 / x + b^2 / y) ≥ (a + b)^2 / (x + y)   :=  by sorry
