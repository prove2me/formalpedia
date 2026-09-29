-- Prove2me | solution 1 for lean_workbook_plus_5920
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:06:38.16078+00:00
-- url     : https://prove2.me/submissions/f27581fe-bb6f-4a1a-9d34-d554264aef34

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (c d ψ₁ ψ₂ : ℝ) : ψ₁^2 * c^2 + ψ₂^2 * d^2 ≥ -2 * c * d * ψ₁ * ψ₂ := by
  nlinarith [sq_nonneg (c * ψ₁ + d * ψ₂)]
