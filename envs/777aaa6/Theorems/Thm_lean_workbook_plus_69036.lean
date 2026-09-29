-- Prove2me | Theorems.Thm_lean_workbook_plus_69036
-- name    : lean_workbook_plus_69036
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/e2d3ba09-80c4-49cb-99f4-017716bed621
-- statement:
--   7. $ \cos^{2}x=\frac{1+\cos 2x}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69036 : ∀ x : ℝ, (Real.cos x)^2 = (1 + Real.cos (2 * x)) / 2   :=  by sorry
