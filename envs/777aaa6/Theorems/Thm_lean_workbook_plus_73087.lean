-- Prove2me | Theorems.Thm_lean_workbook_plus_73087
-- name    : lean_workbook_plus_73087
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/67704f6f-4805-4024-8c4b-8daac72dc664
-- statement:
--   with equality iff $ \sin A \cos B = \sin B \cos A \Longrightarrow \sin (A-B) = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73087 :
  ∀ A B : ℝ, (sin A * cos B = sin B * cos A) ↔ sin (A - B) = 0   :=  by sorry
