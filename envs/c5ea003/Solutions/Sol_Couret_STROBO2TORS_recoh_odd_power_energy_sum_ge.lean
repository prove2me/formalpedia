-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_odd_power_energy_sum_ge
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:57:03.794789+00:00
-- url     : https://prove2.me/submissions/d13c3b39-9158-4c84-9581-83f68a6143f9

import Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_energy_sum
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































/-- Without an opposite pair, every pair contribution is nonnegative. -/
theorem recoh_odd_pair_correlation_nonneg (a b : ℂ) (h : a ≠ -b) :
    0 ≤ recohOddPairCorrelation a b := by
  classical
  simp only [recohOddPairCorrelation, h, if_false, sub_zero]
  split_ifs <;> norm_num

/-- No opposite pair forces average squared magnitude at least three. -/
theorem p2m_local_recoh_odd_power_energy_sum_ge (m : ℕ) (hm : 0 < m) (a b c : ℂ)
    (ha : a ^ (2 * m) = 1) (hb : b ^ (2 * m) = 1)
    (hc : c ^ (2 * m) = 1) (hop : ¬ RecohHasOppositePair a b c) :
    3 * (m : ℝ) ≤ ∑ j ∈ Finset.range m, recohOddPowerEnergy a b c j := by
  have hab : a ≠ -b := fun h => hop (Or.inl h)
  have hac : a ≠ -c := fun h => hop (Or.inr (Or.inl h))
  have hbc : b ≠ -c := fun h => hop (Or.inr (Or.inr h))
  rw [recoh_odd_power_energy_sum m hm a b c ha hb hc]
  have hcorr : 0 ≤ recohOddPairCorrelation a b + recohOddPairCorrelation a c +
      recohOddPairCorrelation b c := by
    linarith [recoh_odd_pair_correlation_nonneg a b hab,
      recoh_odd_pair_correlation_nonneg a c hac,
      recoh_odd_pair_correlation_nonneg b c hbc]
  have hmreal : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith









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
            Not (Couret.STROBO2TORS.RecohHasOppositePair a b c) →
              @LE.le.{0} Real Real.instLE
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 3)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                  (@Nat.cast.{0} Real Real.instNatCast m))
                (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Finset.range m) fun j =>
                  Couret.STROBO2TORS.recohOddPowerEnergy a b c j) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_odd_power_energy_sum_ge

