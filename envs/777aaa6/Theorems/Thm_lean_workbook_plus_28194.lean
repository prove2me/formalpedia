-- Prove2me | Theorems.Thm_lean_workbook_plus_28194
-- name    : lean_workbook_plus_28194
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/9351a4ad-1125-42eb-bd59-376889db24aa
-- statement:
--   $ \cos\alpha\cos\beta = \frac{1}{2}\left( \cos (\alpha-\beta )+\cos (\alpha+\beta ) \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28194 (α β : ℝ) : cos α * cos β = 1 / 2 * (cos (α - β) + cos (α + β))   :=  by sorry
