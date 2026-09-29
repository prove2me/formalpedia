-- Prove2me | Theorems.Thm_lean_workbook_plus_81050
-- name    : lean_workbook_plus_81050
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/64d33ede-5945-4d39-9de2-a2a83dccc79b
-- statement:
--   For $x > 0$, prove the inequality:\n$\frac{1}{4x^2+1}\geq \frac{-8x}{25}+\frac{13}{25}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81050 (x : ℝ) (h₀ : 0 < x) : 1 / (4 * x^2 + 1) ≥ -8 * x / 25 + 13 / 25   :=  by sorry
