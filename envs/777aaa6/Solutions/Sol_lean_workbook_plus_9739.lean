-- Prove2me | solution 1 for lean_workbook_plus_9739
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:49:51.551407+00:00
-- url     : https://prove2.me/submissions/876ca538-d708-49e3-b7e2-d46fae8c8186

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
set_option autoImplicit false
theorem solution : ¬ (∀ c a x d b y z₁ z₂ : ℝ,  z₁ = c - a - x ∧ z₂ = d - b - y → (2 * c - 2 * a - z₁) ^ 2 + (2 * d - 2 * b - z₂) ^ 2 = z₁ ^ 2 + z₂ ^ 2 ∧ z₁ ^ 2 + z₂ ^ 2 = (2 * a + z₁) ^ 2 + (2 * b + z₂) ^ 2) := by
  intro h
  have hh := h 1 0 1 0 0 0 0 0 (by norm_num)
  have he := hh.1
  norm_num at he <;> grind
