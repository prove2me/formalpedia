-- Prove2me | solution 1 for lean_workbook_plus_45535
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:29:31.034855+00:00
-- url     : https://prove2.me/submissions/1cc44f35-6957-4ac5-aa30-bc3f02b8b08a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ¬ ∃ v : ℤ, v > 0 ∧ v^3 + 2 * v^2 - 1 = 0 := by
  rintro ⟨v, hv, he⟩
  have hv1 : 1 ≤ v := by omega
  have h2 : 1 ≤ v^2 := one_le_pow₀ hv1
  have h3 : 1 ≤ v^3 := one_le_pow₀ hv1
  omega
