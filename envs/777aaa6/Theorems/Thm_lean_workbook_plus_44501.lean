-- Prove2me | Theorems.Thm_lean_workbook_plus_44501
-- name    : lean_workbook_plus_44501
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/55b54ac4-21cc-4ac7-a688-1fb51834e077
-- statement:
--   Let $0\le x\le 1$ . Prove that $2sinx+tanx- 3x>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44501 : ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 → 2 * Real.sin x + Real.tan x - 3 * x > 0   :=  by sorry
