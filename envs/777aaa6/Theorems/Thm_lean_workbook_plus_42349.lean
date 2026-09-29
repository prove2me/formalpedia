-- Prove2me | Theorems.Thm_lean_workbook_plus_42349
-- name    : lean_workbook_plus_42349
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/7ec8689f-dad7-422f-b98d-f8e6b9c1ac78
-- statement:
--   Prove the lemma: $\sin \alpha \cdot \sin \gamma + \sin \beta \cdot \sin (\alpha + \beta + \gamma) = \sin (\alpha + \beta) \cdot \sin (\beta + \gamma).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42349 {α β γ : ℝ} : sin α * sin γ + sin β * sin (α + β + γ) = sin (α + β) * sin (β + γ)   :=  by sorry
