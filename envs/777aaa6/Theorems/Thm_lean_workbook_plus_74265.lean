-- Prove2me | Theorems.Thm_lean_workbook_plus_74265
-- name    : lean_workbook_plus_74265
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/6e78df47-bf3b-43a1-a5e2-6b967059c69f
-- statement:
--   $\Longleftrightarrow \sin \frac{1}{2} \theta = 0 \bigvee \cos \frac{1}{2} \theta = 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74265 : ∀ θ : ℝ, sin (1 / 2 * θ) = 0 ∨ cos (1 / 2 * θ) = 1   :=  by sorry
