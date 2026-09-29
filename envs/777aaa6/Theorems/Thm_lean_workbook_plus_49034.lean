-- Prove2me | Theorems.Thm_lean_workbook_plus_49034
-- name    : lean_workbook_plus_49034
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/421d963b-082e-4133-b5bc-c067fb03161c
-- statement:
--   Using the Cauchy-Schwarz Inequality, prove that for any real numbers a and b, and any angle x, the following inequality holds: \\(asinx + bcosx \leq \sqrt{a^2 + b^2}\\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49034 (a b : ℝ) (x : ℝ) : a * Real.sin x + b * Real.cos x ≤ Real.sqrt (a ^ 2 + b ^ 2)   :=  by sorry
