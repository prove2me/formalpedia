-- Prove2me | Theorems.Thm_lean_workbook_plus_17201
-- name    : lean_workbook_plus_17201
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/d24b602b-978a-4710-8d09-b9f5ff907354
-- statement:
--   Prove that $\cos^2 \theta =\frac{1+\cos 2\theta}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17201 : ∀ θ : ℝ, (cos θ)^2 = (1 + cos (2 * θ)) / 2   :=  by sorry
