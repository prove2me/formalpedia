-- Prove2me | solution 1 for lean_workbook_plus_35816
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:03:22.339979+00:00
-- url     : https://prove2.me/submissions/a2a008b8-ba59-486c-a82b-9c6c727b121f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℤ) : gcd a b = 1 ↔ ∃ x y : ℤ, a * x + b * y = 1 := by
  rw [← Int.coe_gcd]
  norm_cast
  simpa only [IsCoprime, mul_comm] using (Int.isCoprime_iff_gcd_eq_one (m := a) (n := b)).symm
