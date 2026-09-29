-- Prove2me | solution 1 for lean_workbook_plus_12562
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:03:27.521803+00:00
-- url     : https://prove2.me/submissions/74a7a81e-a488-4c2f-bc2e-c64ba90aa591

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℤ) : gcd a b = 1 ↔ ∃ h k : ℤ, h * a + k * b = 1 := by
  rw [← Int.coe_gcd]
  norm_cast
  exact (Int.isCoprime_iff_gcd_eq_one (m := a) (n := b)).symm
