-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_odd_power_sum
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:31.099069+00:00
-- url     : https://prove2.me/submissions/cf633440-87fc-4d2c-a779-89ad55ff437d

import Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
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











/-- Telescoping identity for the unnormalized odd-power sum. -/
theorem recoh_odd_power_sum_mul (m : ℕ) (z : ℂ) :
    (∑ j ∈ Finset.range m, z ^ (2 * j + 1)) * (z ^ 2 - 1) =
      z ^ (2 * m + 1) - z := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, pow_add]
      ring

/-- The odd-power geometric sum is nonzero only at the two real roots. -/
theorem p2m_local_recoh_odd_power_sum (m : ℕ) (z : ℂ)
    (hz : z ^ (2 * m) = 1) :
    (∑ j ∈ Finset.range m, z ^ (2 * j + 1)) =
      if z = 1 then (m : ℂ) else if z = -1 then -(m : ℂ) else 0 := by
  classical
  by_cases h1 : z = 1
  · simp [h1]
  by_cases hn : z = -1
  · rw [if_neg h1, if_pos hn, hn]
    simp [pow_add, pow_mul]
  simp only [h1, hn, if_false]
  have hfactor : z ^ 2 - 1 ≠ 0 := by
    intro h
    have hprod : (z - 1) * (z + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hprod with hleft | hright
    · exact h1 (sub_eq_zero.mp hleft)
    · exact hn (eq_neg_of_add_eq_zero_left hright)
  have htel := recoh_odd_power_sum_mul m z
  rw [pow_add, hz, pow_one, one_mul, sub_self] at htel
  exact (mul_eq_zero.mp htel).resolve_right hfactor





























end Couret.STROBO2TORS


theorem solution : ∀ (m : Nat) (z : Complex),
  @Eq.{1} Complex
      (@HPow.hPow.{0, 0, 0} Complex Nat Complex
        (@instHPow.{0, 0} Complex Nat (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
        z
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) →
    @Eq.{1} Complex
      (@Finset.sum.{0, 0} Nat Complex
        (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Complex
                  (@NormedCommRing.toNonUnitalNormedCommRing.{0} Complex
                    (@NormedField.toNormedCommRing.{0} Complex Complex.instNormedField)))))))
        (Finset.range m) fun j =>
        @HPow.hPow.{0, 0, 0} Complex Nat Complex
          (@instHPow.{0, 0} Complex Nat
            (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
          z
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@ite.{1} Complex
        (@Eq.{1} Complex z (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
        (Complex.instDecidableEq z (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
        (@Nat.cast.{0} Complex Complex.instNatCast m)
        (@ite.{1} Complex
          (@Eq.{1} Complex z
            (@Neg.neg.{0} Complex Complex.instNeg
              (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))))
          (Complex.instDecidableEq z
            (@Neg.neg.{0} Complex Complex.instNeg
              (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))))
          (@Neg.neg.{0} Complex Complex.instNeg (@Nat.cast.{0} Complex Complex.instNatCast m))
          (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_odd_power_sum

