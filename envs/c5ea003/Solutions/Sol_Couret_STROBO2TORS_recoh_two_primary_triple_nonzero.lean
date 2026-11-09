-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_two_primary_triple_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:07.678139+00:00
-- url     : https://prove2.me/submissions/c457bade-a9ee-4f3a-9b14-deed9ff52556

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_power_triple_nonzero
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



/-- Raising the permitted 2-power exponent preserves the root equation. -/
theorem recoh_two_power_root_mono
    {m n : ℕ} (z : ℂ) (hmn : m ≤ n)
    (hz : z ^ (2 ^ m) = 1) : z ^ (2 ^ n) = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add, pow_mul, hz, one_pow]





/-- A version allowing a different 2-power exponent for each root. -/
theorem p2m_local_recoh_two_primary_triple_nonzero
    (a b c : ℂ)
    (ha : ∃ n : ℕ, a ^ (2 ^ n) = 1)
    (hb : ∃ n : ℕ, b ^ (2 ^ n) = 1)
    (hc : ∃ n : ℕ, c ^ (2 ^ n) = 1) :
    a + b + c ≠ 0 := by
  obtain ⟨na, ha⟩ := ha
  obtain ⟨nb, hb⟩ := hb
  obtain ⟨nc, hc⟩ := hc
  apply recoh_two_power_triple_nonzero (na + nb + nc) a b c
  · exact recoh_two_power_root_mono a (by omega) ha
  · exact recoh_two_power_root_mono b (by omega) hb
  · exact recoh_two_power_root_mono c (by omega) hc

end Couret.STROBO2TORS


theorem solution : ∀ (a b c : Complex),
  (@Exists.{1} Nat fun n =>
      @Eq.{1} Complex
        (@HPow.hPow.{0, 0, 0} Complex Nat Complex
          (@instHPow.{0, 0} Complex Nat
            (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
          a
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
    (@Exists.{1} Nat fun n =>
        @Eq.{1} Complex
          (@HPow.hPow.{0, 0, 0} Complex Nat Complex
            (@instHPow.{0, 0} Complex Nat
              (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
            b
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
          (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
      (@Exists.{1} Nat fun n =>
          @Eq.{1} Complex
            (@HPow.hPow.{0, 0, 0} Complex Nat Complex
              (@instHPow.{0, 0} Complex Nat
                (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
              c
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
            (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
        @Ne.{1} Complex
          (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) a b) c)
          (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_two_primary_triple_nonzero

