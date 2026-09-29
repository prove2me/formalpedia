-- Prove2me | Theorems.Thm_lean_workbook_plus_29615
-- name    : lean_workbook_plus_29615
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/f2c49215-e828-442d-abff-a04d1bce685e
-- statement:
--   Simplify the integral using partial fractions: \\( \frac{1}{x^2+x-6} = \frac{1}{5}\left (\frac{1}{x-2}-\frac{1}{x+3}\right ) \\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29615 : ∀ x : ℝ, x^2 + x - 6 ≠ 0 → 1 / (x^2 + x - 6) = 1/5 * (1/(x - 2) - 1/(x + 3))   :=  by sorry
