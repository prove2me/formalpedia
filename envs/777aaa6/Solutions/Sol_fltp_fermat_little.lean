-- Prove2me | solution 1 for fltp_fermat_little
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T10:00:03.875039+00:00
-- url     : https://prove2.me/submissions/0371734c-c42f-4e8e-b9eb-fc20f72bc53b

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

-- Fermat's Little Theorem for any prime p: p | a^p - a for all integers a.
theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℤ) : (p : ℤ) ∣ a^p - a := by
  have hmod : ∀ x : ZMod p, x^p = x := by
    intro x
    have h := FiniteField.pow_card (K := ZMod p) x
    rwa [ZMod.card p] at h
  have h2 : ((a^p - a : ℤ) : ZMod p) = 0 := by
    push_cast; rw [hmod]; exact sub_self _
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a^p - a) p).mp h2
