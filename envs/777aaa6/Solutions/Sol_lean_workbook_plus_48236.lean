-- Prove2me | solution 1 for lean_workbook_plus_48236
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:48:20.301054+00:00
-- url     : https://prove2.me/submissions/4cdc7e2e-0e29-4c60-9129-5488f97d30c0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution : ∀ n : ℕ, ∀ z : Fin n → ℂ,
    ∑ i, ‖z i‖ ≥ ‖∑ i, z i‖ := by
  intro n z
  exact norm_sum_le _ _

#print axioms solution
