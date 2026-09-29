-- Prove2me | solution 1 for SteinENT.two_squares_criterion
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:26:47.986939+00:00
-- url     : https://prove2.me/submissions/58a78459-cc28-499f-8a50-809e5ee0b5e2

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace SteinENT

private theorem integer_representation_iff_natural (n : ℕ) :
    (∃ x y : ℤ, (n : ℤ) = x ^ 2 + y ^ 2) ↔
      ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  constructor
  · rintro ⟨x, y, h⟩
    refine ⟨x.natAbs, y.natAbs, ?_⟩
    zify
    simpa only [Int.natCast_natAbs, sq_abs] using h
  · rintro ⟨x, y, h⟩
    refine ⟨x, y, ?_⟩
    exact_mod_cast h

theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    (∃ x y : ℤ, (n : ℤ) = x ^ 2 + y ^ 2) ↔
      ∀ p : ℕ, p.Prime → p ∣ n → p % 4 = 3 → Even (n.factorization p) := by
  rw [integer_representation_iff_natural, Nat.eq_sq_add_sq_iff]
  constructor
  · intro h p hp hpn hmod
    rw [Nat.factorization_def n hp]
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩) hmod
  · intro h p hpn hmod
    have hp := Nat.prime_of_mem_primeFactors hpn
    rw [← Nat.factorization_def n hp]
    exact h p hp (Nat.dvd_of_mem_primeFactors hpn) hmod

end SteinENT
