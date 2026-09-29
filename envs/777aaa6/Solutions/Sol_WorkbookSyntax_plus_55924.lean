-- Prove2me | solution 1 for WorkbookSyntax.plus_55924
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:16.448601+00:00
-- url     : https://prove2.me/submissions/5d2c94f4-4aa6-4734-839a-b28b25084bf9

import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution (a : ℤ) :
    ∑ i ∈ Finset.range 7, (a + i) ^ 3 ≡ 0 [ZMOD 7]   := by
  have h : (∑ i ∈ Finset.range 7, (a + i) ^ 3) = 7 * (a^3 + 9*a^2 + 39*a + 63) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [h]
  exact Int.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
#print axioms solution
