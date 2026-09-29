-- Prove2me | Theorems.Thm_lean_workbook_plus_33989
-- name    : lean_workbook_plus_33989
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/af4eea19-1de0-498c-8503-700adad5a54b
-- statement:
--   Setting $y=\cos x$ and squaring, this becomes $4y^4-4y^3-6y^2+4y+3=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33989 : ∀ x : ℝ, (4 * cos x ^ 4 - 4 * cos x ^ 3 - 6 * cos x ^ 2 + 4 * cos x + 3 = 0)   :=  by sorry
