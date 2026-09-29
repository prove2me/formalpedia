-- Prove2me | Theorems.Thm_lean_workbook_plus_4832
-- name    : lean_workbook_plus_4832
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/9a2fe3f1-3df8-4aee-8778-8c2e9ead928a
-- statement:
--   Prove the identity $\cos^{2}(y) = \frac{\cos(2y)+1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4832 : ∀ y : ℝ, cos y ^ 2 = (cos (2 * y) + 1) / 2   :=  by sorry
