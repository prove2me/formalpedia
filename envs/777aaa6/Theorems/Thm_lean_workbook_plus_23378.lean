-- Prove2me | Theorems.Thm_lean_workbook_plus_23378
-- name    : lean_workbook_plus_23378
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/369f6b7f-7a6a-4cdf-afb1-ac47aae96830
-- statement:
--   Solve the trigonometric equation - \n $$\sin^6x+\sin^4x\cdot \cos^2x=\sin^2x \cdot \cos^3x+\sin x \cdot \cos^5x$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23378 : ∀ x : ℝ, (sin x)^6 + (sin x)^4 * (cos x)^2 = (sin x)^2 * (cos x)^3 + sin x * (cos x)^5 ↔ ∃ n : ℤ, x = 2 * n * π ∨ x = π / 4 + n * π   :=  by sorry
