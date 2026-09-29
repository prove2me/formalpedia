-- Prove2me | solution 1 for lean_workbook_plus_3127
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:27:22.400721+00:00
-- url     : https://prove2.me/submissions/5b0bd4da-0669-4c2c-8c5a-84ce4956a3e4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y : ℝ)
  (h₀ : 0 ≤ 1 + x^2 + y^2 + x^2 * y^2)
  (h₁ : 0 ≤ 2 + x^2 + y^2)
  (h₂ : 1 + x^2 + y^2 + x^2 * y^2 ≠ 0)
  (h₃ : 2 + x^2 + y^2 ≠ 0)
  (h₄ : 0 ≤ x * y) :
  (2 * x * y - 1) * (x * y - 1) ≤ 0 ↔ x * y ∈ Set.Icc (1 / 2) 1 := by
  clear h₀ h₁ h₂ h₃ h₄
  constructor
  · intro h
    constructor
    · nlinarith [sq_nonneg (x * y - (1 : ℝ) / 2)]
    · nlinarith [sq_nonneg (x * y - 1)]
  · rintro ⟨hlo, hhi⟩
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
