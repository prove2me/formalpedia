-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_odd_pair_sum
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:44:09.137861+00:00
-- url     : https://prove2.me/submissions/989968c9-de61-4f80-a8ec-38efc019cdef

import Definitions.Def_Couret_RecohOddPowerAverage_39ee40b78d83
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_STROBO2TORS_recoh_odd_power_sum
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















/-- Unit-modulus conjugation gives the inverse without division. -/
theorem recoh_unit_conj_mul (z : ℂ) (hz : ‖z‖ = 1) :
    star z * z = 1 := by
  simpa [hz, mul_comm] using Complex.mul_conj' z

/-- A pair ratio equals one exactly for equal phases. -/
theorem recoh_unit_pair_eq_one_iff (a b : ℂ) (hb : ‖b‖ = 1) :
    a * star b = 1 ↔ a = b := by
  have hbb := recoh_unit_conj_mul b hb
  constructor
  · intro h
    calc
      a = (a * star b) * b := by rw [mul_assoc, hbb, mul_one]
      _ = b := by rw [h, one_mul]
  · rintro rfl
    simpa [mul_comm] using hbb

/-- A pair ratio equals minus one exactly for opposite phases. -/
theorem recoh_unit_pair_eq_neg_one_iff (a b : ℂ) (hb : ‖b‖ = 1) :
    a * star b = -1 ↔ a = -b := by
  have hbb := recoh_unit_conj_mul b hb
  constructor
  · intro h
    calc
      a = (a * star b) * b := by rw [mul_assoc, hbb, mul_one]
      _ = -b := by rw [h, neg_one_mul]
  · rintro rfl
    rw [neg_mul, mul_comm b, hbb]

/-- Odd-power orthogonality for a pair of roots of the same even order. -/
theorem p2m_local_recoh_odd_pair_sum (m : ℕ) (a b : ℂ)
    (ha : a ^ (2 * m) = 1) (hb : b ^ (2 * m) = 1)
    (hbn : ‖b‖ = 1) :
    (∑ j ∈ Finset.range m, ((a * star b) ^ (2 * j + 1)).re) =
      (m : ℝ) * recohOddPairCorrelation a b := by
  classical
  have hstar : (star b) ^ (2 * m) = 1 := by
    simpa only [map_pow, map_one] using congrArg (starRingEnd ℂ) hb
  have hroot : (a * star b) ^ (2 * m) = 1 := by
    rw [mul_pow, ha, hstar, one_mul]
  have hsum := congrArg Complex.re (recoh_odd_power_sum m (a * star b) hroot)
  have hzero : b ≠ 0 := by
    intro h
    simp [h] at hbn
  have hnotboth : a = b → a ≠ -b := by
    intro hab hop
    have h : b = -b := hab.symm.trans hop
    have htwo : (2 : ℂ) * b = 0 := by linear_combination h
    exact hzero ((mul_eq_zero.mp htwo).resolve_left (by norm_num))
  simp only [recoh_unit_pair_eq_one_iff a b hbn,
    recoh_unit_pair_eq_neg_one_iff a b hbn] at hsum
  by_cases hab : a = b
  · rw [if_pos hab] at hsum
    rw [recohOddPairCorrelation, if_pos hab, if_neg (hnotboth hab)]
    simpa using hsum
  by_cases hop : a = -b
  · rw [if_neg hab, if_pos hop] at hsum
    rw [recohOddPairCorrelation, if_neg hab, if_pos hop]
    simpa using hsum
  · rw [if_neg hab, if_neg hop] at hsum
    rw [recohOddPairCorrelation, if_neg hab, if_neg hop]
    simpa using hsum





















end Couret.STROBO2TORS


theorem solution : ∀ (m : Nat) (a b : Complex),
  @Eq.{1} Complex
      (@HPow.hPow.{0, 0, 0} Complex Nat Complex
        (@instHPow.{0, 0} Complex Nat (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
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
      @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm b)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
        @Eq.{1} Real
          (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Finset.range m) fun j =>
            Complex.re
              (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                (@instHPow.{0, 0} Complex Nat
                  (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) a
                  (@Star.star.{0} Complex
                    (@InvolutiveStar.toStar.{0} Complex
                      (@StarAddMonoid.toInvolutiveStar.{0} Complex
                        (@AddCommMonoid.toAddMonoid.{0} Complex
                          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                  (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Complex
                                    (@NormedCommRing.toNonUnitalNormedCommRing.{0} Complex
                                      (@NormedField.toNormedCommRing.{0} Complex Complex.instNormedField))))))))
                        (@StarRing.toStarAddMonoid.{0} Complex
                          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Complex
                                  (@NormedCommRing.toNonUnitalNormedCommRing.{0} Complex
                                    (@NormedField.toNormedCommRing.{0} Complex Complex.instNormedField))))))
                          Complex.instStarRing)))
                    b))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast m)
            (Couret.STROBO2TORS.recohOddPairCorrelation a b)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_odd_pair_sum

