-- Prove2me | Theorems.Thm_lean_workbook_plus_27421
-- name    : lean_workbook_plus_27421
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/162acfa7-eb49-48cb-990b-4af763e425c1
-- statement:
--   Solve the equation for $\theta$: $\cos 3\theta=\frac 12$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27421 : ∀ θ : ℝ, cos 3*θ = 1/2 ↔ θ = π/6 ∨ θ = π/2 ∨ θ = 5*π/6   :=  by sorry
