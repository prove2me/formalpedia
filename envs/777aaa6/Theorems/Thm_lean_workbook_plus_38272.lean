-- Prove2me | Theorems.Thm_lean_workbook_plus_38272
-- name    : lean_workbook_plus_38272
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/11795fe7-5360-46b1-a5ad-a5ac604a59ad
-- statement:
--   Compare with $3^{k+1}((k+1)!)^2$: $3(k+1)^{k+1}>3^{k+1}((k+1)!)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38272 : ∀ k : ℕ, k ≥ 1 → (3 : ℝ) * (k + 1) ^ (k + 1) > 3 ^ (k + 1) * (k + 1)! ^ 2   :=  by sorry
