-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_odd_power_energy_sum
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:12.316799+00:00
-- url     : https://prove2.me/submissions/179497af-cd89-423f-8950-0a7cd575fa72

import Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_pair_sum
import Theorems.Thm_Couret_STROBO2TORS_recoh_unit_three_energy
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Averaging odd powers of three roots of even order

The order is written `2 * m`, with `0 < m`.  This includes the entire
2-primary case and keeps the geometric-sum argument independent of a
particular presentation of the order.  Repeated complex phases are allowed.

The energy at index `j` is the squared norm of the reading at exponent
`2 * j + 1`.  An opposite pair makes every such energy equal to one.
Otherwise their sum is at least `3 * m`, and some energy is at least three.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

























/-- Complete odd-power average identity.  Each correlation is one for an
equal pair, minus one for an opposite pair, and zero otherwise. -/
theorem p2m_local_recoh_odd_power_energy_sum (m : ℕ) (hm : 0 < m) (a b c : ℂ)
    (ha : a ^ (2 * m) = 1) (hb : b ^ (2 * m) = 1)
    (hc : c ^ (2 * m) = 1) :
    (∑ j ∈ Finset.range m, recohOddPowerEnergy a b c j) =
      (m : ℝ) * (3 + 2 * (recohOddPairCorrelation a b +
        recohOddPairCorrelation a c + recohOddPairCorrelation b c)) := by
  have horder : 2 * m ≠ 0 := by omega
  have han := Complex.norm_eq_one_of_pow_eq_one ha horder
  have hbn := Complex.norm_eq_one_of_pow_eq_one hb horder
  have hcn := Complex.norm_eq_one_of_pow_eq_one hc horder
  have hexpand (j : ℕ) : recohOddPowerEnergy a b c j =
      3 + 2 * (((a * star b) ^ (2 * j + 1)).re +
        ((a * star c) ^ (2 * j + 1)).re + ((b * star c) ^ (2 * j + 1)).re) := by
    simpa only [recohOddPowerEnergy, mul_pow, star_pow] using
      recoh_unit_three_energy (a ^ (2 * j + 1)) (b ^ (2 * j + 1))
        (c ^ (2 * j + 1)) (by simp [norm_pow, han])
        (by simp [norm_pow, hbn]) (by simp [norm_pow, hcn])
  simp_rw [hexpand]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [recoh_odd_pair_sum m a b ha hb hbn,
    recoh_odd_pair_sum m a c ha hc hcn,
    recoh_odd_pair_sum m b c hb hc hcn]
  simp
  ring

















end Couret.STROBO2TORS


theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀ (a b c : Complex),
      @Eq.{1} Complex
          (@HPow.hPow.{0, 0, 0} Complex Nat Complex
            (@instHPow.{0, 0} Complex Nat
              (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
            a
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
          (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
        @Eq.{1} Complex
            (@HPow.hPow.{0, 0, 0} Complex Nat Complex
              (@instHPow.{0, 0} Complex Nat
                (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
              b
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
            (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
          @Eq.{1} Complex
              (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                (@instHPow.{0, 0} Complex Nat
                  (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                c
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
              (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
            @Eq.{1} Real
              (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Finset.range m) fun j =>
                Couret.STROBO2TORS.recohOddPowerEnergy a b c j)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast m)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@OfNat.ofNat.{0} Real (nat_lit 3)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (Couret.STROBO2TORS.recohOddPairCorrelation a b)
                        (Couret.STROBO2TORS.recohOddPairCorrelation a c))
                      (Couret.STROBO2TORS.recohOddPairCorrelation b c))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_odd_power_energy_sum

