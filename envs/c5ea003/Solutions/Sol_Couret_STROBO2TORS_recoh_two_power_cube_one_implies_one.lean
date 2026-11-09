-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_two_power_cube_one_implies_one
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:31:44.23954+00:00
-- url     : https://prove2.me/submissions/6ae21040-098e-409a-84d8-18fe17041f4d

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_Couret_STROBO2TORS_recoh_square_cube_one_implies_one

set_option autoImplicit false

/-! A candidate generalization: a complex number of simultaneous
2-power and third order is 1. This is NOT yet the no-three-term
cancellation theorem, nor the character-bank upper bound. -/

namespace Couret.STROBO2TORS

theorem p2m_local_recoh_two_power_cube_one_implies_one
    (n : ℕ) (z : ℂ)
    (hpow : z ^ (2 ^ n) = 1)
    (hcube : z ^ 3 = 1) : z = 1 := by
  induction n generalizing z with
  | zero =>
      simpa using hpow
  | succ n ih =>
      have hsq : (z ^ 2) ^ (2 ^ n) = 1 := by
        calc
          (z ^ 2) ^ (2 ^ n) = z ^ (2 ^ n * 2) := by
            rw [← pow_mul]
            congr 1
            omega
          _ = z ^ (2 ^ (n + 1)) := by rw [pow_succ]
          _ = 1 := hpow
      have hcubesq : (z ^ 2) ^ 3 = 1 := by
        calc
          (z ^ 2) ^ 3 = (z ^ 3) ^ 2 := by ring
          _ = 1 := by rw [hcube]; norm_num
      have htwo : z ^ 2 = 1 := ih (z ^ 2) hsq hcubesq
      exact recoh_square_cube_one_implies_one z htwo hcube

end Couret.STROBO2TORS


theorem solution : ∀ (n : Nat) (z : Complex),
  @Eq.{1} Complex
      (@HPow.hPow.{0, 0, 0} Complex Nat Complex
        (@instHPow.{0, 0} Complex Nat (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
        z
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
    @Eq.{1} Complex
        (@HPow.hPow.{0, 0, 0} Complex Nat Complex
          (@instHPow.{0, 0} Complex Nat
            (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
          z (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
      @Eq.{1} Complex z (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_two_power_cube_one_implies_one

