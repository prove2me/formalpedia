-- Prove2me | Theorems.Thm_lean_workbook_plus_60365
-- name    : lean_workbook_plus_60365
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/6b47a0ca-c8e4-40be-a93d-ca1d3ee56336
-- statement:
--   Prove that $\cos{3x}=-\frac{1}{2}$ implies $8\cos^3x-6\cos{x}+1=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60365 (x : ℝ) (h : Real.cos (3 * x) = -1 / 2) :
  8 * (Real.cos x)^3 - 6 * Real.cos x + 1 = 0   :=  by sorry
