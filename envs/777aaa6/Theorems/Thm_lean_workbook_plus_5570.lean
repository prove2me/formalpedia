-- Prove2me | Theorems.Thm_lean_workbook_plus_5570
-- name    : lean_workbook_plus_5570
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/4d99d130-ef96-427c-86fa-f977f7cb619c
-- statement:
--   Prove the identity $e^{i\alpha}=\cos \alpha + i\sin \alpha$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5570 : ∀ α : ℝ, exp (α * I) = cos α + sin α * I   :=  by sorry
