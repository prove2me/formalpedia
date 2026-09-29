-- Prove2me | Theorems.Thm_lean_workbook_plus_374
-- name    : lean_workbook_plus_374
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/d44b8c02-156e-4e2d-975b-878a98254b4e
-- statement:
--   So required expression is $\frac{2\cos x}{|\sin x|}\frac{2\sin x}{|\cos x|}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_374 (x : ℝ) (hx: x ≠ 0) (h2x: x ≠ π/2) : 2 * cos x / abs (sin x) * (2 * sin x / abs (cos x)) = 4 * cos x * sin x / (abs (sin x) * abs (cos x))   :=  by sorry
