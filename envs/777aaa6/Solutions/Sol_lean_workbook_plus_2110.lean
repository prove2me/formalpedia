-- Prove2me | solution 1 for lean_workbook_plus_2110
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:26:16.618745+00:00
-- url     : https://prove2.me/submissions/e101ad36-a838-48eb-8f85-cb359aafb61c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (α β γ : ℝ) (h : α + β + γ ≥ 6) (habc : α * β * γ = α + β + γ + 2) : α * β * γ ≥ 8 := by
  (intros; linarith)
