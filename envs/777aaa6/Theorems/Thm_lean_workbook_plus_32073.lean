-- Prove2me | Theorems.Thm_lean_workbook_plus_32073
-- name    : lean_workbook_plus_32073
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/9d0e25e9-ca42-4c77-932b-e0ca781f6e82
-- statement:
--   Prove that $cos^4x=\frac{1}{8}cos4x+\frac{1}{2}cos2x+\frac{3}{8}$ using the trigonometric form of a complex number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32073 (x : ℝ) : (cos x)^4 = 1 / 8 * cos (4 * x) + 1 / 2 * cos (2 * x) + 3 / 8   :=  by sorry
