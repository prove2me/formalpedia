-- Prove2me | solution 1 for lean_workbook_plus_50646
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:20:06.790459+00:00
-- url     : https://prove2.me/submissions/a2e44baa-a474-48e5-b0fc-698fa0a326b3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (m₁ m₂ v₀ V : ℝ)
  (h₀ : m₁ ≠ 0 ∧ m₂ ≠ 0)
  (h₁ : (m₁ + m₂) ≠ 0)
  (h₂ : m₁ * v₀ = (m₁ + m₂) * V) :
  V = m₁ * v₀ / (m₁ + m₂) := by
  (intros; simp_all)
