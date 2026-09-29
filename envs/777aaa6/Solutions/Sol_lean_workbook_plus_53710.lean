-- Prove2me | solution 1 for lean_workbook_plus_53710
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:51.736113+00:00
-- url     : https://prove2.me/submissions/c6fdbd66-ba77-4fe3-bd70-6b387141ed82

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x₁ x₂ y₁ y₂ y₃ y₄ : ℝ) (h₁ : y₁ * y₂ * y₃ * y₄ = 1) (h₂ : x₁ * x₂ * y₁ * y₂ = 1) : x₁ * x₂ = y₃ * y₄ := by
  intros
  grind
