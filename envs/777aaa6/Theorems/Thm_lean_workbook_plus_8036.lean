-- Prove2me | Theorems.Thm_lean_workbook_plus_8036
-- name    : lean_workbook_plus_8036
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/12bbca1a-9c2b-4a9a-a91b-af10fd7e10b3
-- statement:
--   Prove the following equation: $\frac{x^2-2x+2}{3x^2-10x+6}+\frac{3x}{x^2+2}=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8036 : ∀ x : ℝ, (x^2 - 2 * x + 2) / (3 * x^2 - 10 * x + 6) + 3 * x / (x^2 + 2) = 1   :=  by sorry
