-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_two_power_triple_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:47:25.582286+00:00
-- url     : https://prove2.me/submissions/7fb2a4bf-6391-4904-89d7-7a24706a9032

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_Couret_STROBO2TORS_recoh_symmetric_three_sum_two_power_impossible
import Theorems.Thm_Couret_STROBO2TORS_recoh_unit_three_sum_pair_zero
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

/-!
# Nonvanishing of three complex roots of 2-power order

The conjugation argument below supplies the symmetric-pair equation
that was an explicit hypothesis in `RecohThreeRootSymmetricGate`.
After normalization by the first root, the coprime-orders gate rules
out a vanishing sum of three roots whose orders divide powers of two.

The three roots need not be distinct. The exponents may differ.
This module proves nonvanishing; it does not assert that a character
bank is optimal or construct the bank required for reconstruction.
-/

namespace Couret.STROBO2TORS





/-- The normalized sum of one and two roots of common 2-power order
cannot vanish. -/
theorem recoh_two_power_normalized_triple_nonzero
    (n : ℕ) (b c : ℂ)
    (hb : b ^ (2 ^ n) = 1) (hc : c ^ (2 ^ n) = 1) :
    1 + b + c ≠ 0 := by
  intro hsum
  have hbn : ‖b‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hb (pow_ne_zero _ (by decide))
  have hcn : ‖c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hc (pow_ne_zero _ (by decide))
  exact recoh_symmetric_three_sum_two_power_impossible n b c hb hsum
    (recoh_unit_three_sum_pair_zero b c hbn hcn hsum)

/-- Three complex roots whose orders divide a common power of two
have a nonzero sum, including repeated roots and exponent zero. -/
theorem p2m_local_recoh_two_power_triple_nonzero
    (n : ℕ) (a b c : ℂ)
    (ha : a ^ (2 ^ n) = 1) (hb : b ^ (2 ^ n) = 1)
    (hc : c ^ (2 ^ n) = 1) :
    a + b + c ≠ 0 := by
  intro hsum
  have ha0 : a ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (pow_ne_zero _ (by decide))] at ha
    exact zero_ne_one ha
  have hba : (b / a) ^ (2 ^ n) = 1 := by simp [div_pow, hb, ha]
  have hca : (c / a) ^ (2 ^ n) = 1 := by simp [div_pow, hc, ha]
  apply recoh_two_power_normalized_triple_nonzero n (b / a) (c / a) hba hca
  calc
    1 + b / a + c / a = (a + b + c) / a := by
      rw [add_div, add_div, div_self ha0]
    _ = 0 := by rw [hsum, zero_div]



end Couret.STROBO2TORS


theorem solution : ∀ (n : Nat) (a b c : Complex),
  @Eq.{1} Complex
      (@HPow.hPow.{0, 0, 0} Complex Nat Complex
        (@instHPow.{0, 0} Complex Nat (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
        a
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
    @Eq.{1} Complex
        (@HPow.hPow.{0, 0, 0} Complex Nat Complex
          (@instHPow.{0, 0} Complex Nat
            (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
          b
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
      @Eq.{1} Complex
          (@HPow.hPow.{0, 0, 0} Complex Nat Complex
            (@instHPow.{0, 0} Complex Nat
              (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
            c
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
          (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
        @Ne.{1} Complex
          (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) a b) c)
          (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_two_power_triple_nonzero

