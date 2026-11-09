-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_unit_three_energy
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:43:58.754148+00:00
-- url     : https://prove2.me/submissions/bd58d2b9-a3c1-441b-95ef-329fd6fc8fc3

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























/-- The squared norm of a three-phase sum expands into three pair terms. -/
theorem p2m_local_recoh_unit_three_energy (a b c : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    ‖a + b + c‖ ^ 2 =
      3 + 2 * ((a * star b).re + (a * star c).re + (b * star c).re) := by
  have han : a.re * a.re + a.im * a.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, ha]
    norm_num
  have hbn : b.re * b.re + b.im * b.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hb]
    norm_num
  have hcn : c.re * c.re + c.im * c.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hc]
    norm_num
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith



















end Couret.STROBO2TORS


theorem solution : ∀ (a b c : Complex),
  @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm a)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
    @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm b)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @Eq.{1} Real (@Norm.norm.{0} Complex Complex.instNorm c)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
        @Eq.{1} Real
          (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid))
            (@Norm.norm.{0} Complex Complex.instNorm
              (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Complex Complex Complex (@instHAdd.{0} Complex Complex.instAdd) a b) c))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                  (Complex.re
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
                        b)))
                  (Complex.re
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
                        c))))
                (Complex.re
                  (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) b
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
                      c)))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_unit_three_energy

