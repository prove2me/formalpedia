-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_square_cube_one_implies_one
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:31:00.906777+00:00
-- url     : https://prove2.me/submissions/964baac8-bb37-4233-b6f9-582e1174055f

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-!
An elementary algebraic gate for the nonvanishing of three 2-primary
complex roots. This file does NOT yet prove the full nonvanishing
theorem or construct the RECOH character bank.
-/

namespace Couret.STROBO2TORS

/-- There is no nontrivial simultaneous square and cube root of one
in a field. This is the n = 1 instance of the coprime-orders gate. -/
theorem p2m_local_recoh_square_cube_one_implies_one
    (z : ℂ) (h2 : z ^ 2 = 1) (h3 : z ^ 3 = 1) :
    z = 1 := by
  have h : z ^ 3 = z ^ 2 * z := by ring
  rw [h2, one_mul] at h
  rw [h3] at h
  exact h.symm





end Couret.STROBO2TORS


theorem solution : ∀ (z : Complex),
  @Eq.{1} Complex
      (@HPow.hPow.{0, 0, 0} Complex Nat Complex
        (@instHPow.{0, 0} Complex Nat (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
        z (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
    @Eq.{1} Complex
        (@HPow.hPow.{0, 0, 0} Complex Nat Complex
          (@instHPow.{0, 0} Complex Nat
            (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
          z (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
      @Eq.{1} Complex z (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_square_cube_one_implies_one

