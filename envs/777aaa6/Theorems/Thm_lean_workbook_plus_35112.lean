-- Prove2me | Theorems.Thm_lean_workbook_plus_35112
-- name    : lean_workbook_plus_35112
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/bf47e91c-b7e8-4561-8f2e-f889b3f77d77
-- statement:
--   Setting $y=\cos x$ and squaring, this becomes $4y^4-4y^3-2y^2+2y=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35112 : ∀ x : ℝ, (4 * cos x ^ 4 - 4 * cos x ^ 3 - 2 * cos x ^ 2 + 2 * cos x) = 0   :=  by sorry
