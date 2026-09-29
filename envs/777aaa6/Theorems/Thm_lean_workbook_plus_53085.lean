-- Prove2me | Theorems.Thm_lean_workbook_plus_53085
-- name    : lean_workbook_plus_53085
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/9905ecd4-3286-4bd6-b86e-1a196d1bbb68
-- statement:
--   Use DeMoivre's Theorem to show that $ \cos4\theta=8\cos^{4}\theta-8\cos^{2}\theta+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53085 : ∀ θ : ℝ, Real.cos (4 * θ) = 8 * (Real.cos θ)^4 - 8 * (Real.cos θ)^2 + 1   :=  by sorry
