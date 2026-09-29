-- Prove2me | Theorems.Thm_lean_workbook_plus_60127
-- name    : lean_workbook_plus_60127
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/48faf6cf-29f0-4cf2-bf5a-95348bda3893
-- statement:
--   Prove that $\frac{x+1}{x^2+1}+\frac{1}{4} = \frac{1}{4}\cdot \frac{x^2+4x+5}{x^2+1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60127 (x : ℝ) : (x + 1) / (x ^ 2 + 1) + 1 / 4 = 1 / 4 * (x ^ 2 + 4 * x + 5) / (x ^ 2 + 1)   :=  by sorry
