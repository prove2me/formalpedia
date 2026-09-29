-- Prove2me | solution 1 for lean_workbook_plus_15094
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:08.947955+00:00
-- url     : https://prove2.me/submissions/032355bb-452a-4cda-a1c4-563a4db7be71

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x : ℝ, (x ^ 2 + 4 ≠ 0 ∧ 16 ≠ 0) →
  (1 / (x ^ 2 + 4) ≥ (4 - x) / 16 ↔ x * (x - 2) ^ 2 ≥ 0) := by
  intro x hx
  have hd : 0 < x^2+4 := by positivity
  constructor
  · intro h
    have hp := (le_div_iff₀ hd).mp h
    nlinarith
  · intro h
    apply (le_div_iff₀ hd).2
    nlinarith
