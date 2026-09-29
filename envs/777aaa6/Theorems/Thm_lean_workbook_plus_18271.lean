-- Prove2me | Theorems.Thm_lean_workbook_plus_18271
-- name    : lean_workbook_plus_18271
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/9753ee5b-32ce-498c-a3d4-2c4c09cf0790
-- statement:
--   Solve for $z$ given $|z|=1$ and $|z-1|=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18271 (z : ℂ) (h₁ : ‖z‖ = 1) (h₂ : ‖z - 1‖ = 1) : ∃ θ : ℝ, z = exp (θ * I) ∨ z = exp (θ * I)   :=  by sorry
