-- Prove2me | Theorems.Thm_lean_workbook_plus_25687
-- name    : lean_workbook_plus_25687
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/a592f0bd-ac51-4e8f-9fac-f4d9da8535e3
-- statement:
--   $1-\\cos^{2}x(1-2\\sin^{2}x) = (1-\\cos^{2}x)+\\frac{1}{2}(2\\sin x\\cos x)^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25687 : 1 - cos x ^ 2 * (1 - 2 * sin x ^ 2) = 1 - cos x ^ 2 + 1 / 2 * (2 * sin x * cos x) ^ 2   :=  by sorry
