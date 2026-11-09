-- Prove2me | solution 1 for Couret.InterIA.Fibres.negacyclic_binomial_product_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:07.970722+00:00
-- url     : https://prove2.me/submissions/8b39a994-3c3d-4721-93ac-61b7e7b2c23e

import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_InterIA_Fibres_ordered_negacyclic_binomial_product_not_dvd
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Coprime.Basic

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial

















/-- Two arbitrary real binomials, not merely a pre-normalised coefficient model. -/
theorem p2m_local_negacyclic_binomial_product_not_dvd (m i j k l : ℕ)
    (hi : i < m) (hj : j < m) (hk : k < m) (hl : l < m)
    (hij : i ≠ j) (hkl : k ≠ l)
    (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    ¬ (X^m+1 : ℝ[X]) ∣
      (monomial i a+monomial j b)*(monomial k c+monomial l d) := by
  rcases lt_or_gt_of_ne hij with hij|hij <;> rcases lt_or_gt_of_ne hkl with hkl|hkl
  · exact ordered_negacyclic_binomial_product_not_dvd m i j k l hij hkl hj hl a b c d ha hb hc
  · simpa only [add_comm (monomial k c) (monomial l d)] using
      ordered_negacyclic_binomial_product_not_dvd m i j l k hij hkl hj hk a b d c ha hb hd
  · simpa only [add_comm (monomial i a) (monomial j b)] using
      ordered_negacyclic_binomial_product_not_dvd m j i k l hij hkl hi hl b a c d hb ha hc
  · simpa only [add_comm (monomial i a) (monomial j b),add_comm (monomial k c) (monomial l d)] using
      ordered_negacyclic_binomial_product_not_dvd m j i l k hij hkl hi hk b a d c hb ha hd

end Couret.InterIA.Fibres

theorem solution : ∀ (m i j k l : Nat),
  @LT.lt.{0} Nat instLTNat i m →
    @LT.lt.{0} Nat instLTNat j m →
      @LT.lt.{0} Nat instLTNat k m →
        @LT.lt.{0} Nat instLTNat l m →
          @Ne.{1} Nat i j →
            @Ne.{1} Nat k l →
              ∀ (a b c d : Real),
                @Ne.{1} Real a (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                  @Ne.{1} Real b (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                    @Ne.{1} Real c (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                      @Ne.{1} Real d (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                        Not
                          (@Dvd.dvd.{0} (@Polynomial.{0} Real Real.semiring)
                            (@semigroupDvd.{0} (@Polynomial.{0} Real Real.semiring)
                              (@SemigroupWithZero.toSemigroup.{0} (@Polynomial.{0} Real Real.semiring)
                                (@NonUnitalSemiring.toSemigroupWithZero.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@NonUnitalCommSemiring.toNonUnitalSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                    (@NonUnitalCommRing.toNonUnitalCommSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                      (@CommRing.toNonUnitalCommRing.{0} (@Polynomial.{0} Real Real.semiring)
                                        (@Polynomial.commRing.{0} Real Real.commRing)))))))
                            (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                              (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.instAdd.{0} Real Real.semiring))
                              (@HPow.hPow.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                                (@Polynomial.{0} Real Real.semiring)
                                (@instHPow.{0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                                  (@Monoid.toPow.{0} (@Polynomial.{0} Real Real.semiring)
                                    (@Semiring.toMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                      (@Polynomial.semiring.{0} Real Real.semiring))))
                                (@Polynomial.X.{0} Real Real.semiring) m)
                              (@OfNat.ofNat.{0} (@Polynomial.{0} Real Real.semiring) (nat_lit 1)
                                (@One.toOfNat1.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.instOne.{0} Real Real.semiring))))
                            (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                              (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                              (@instHMul.{0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.instMul.{0} Real Real.semiring))
                              (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.instAdd.{0} Real Real.semiring))
                                (@DFunLike.coe.{1, 1, 1}
                                  (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Real
                                    (@Polynomial.{0} Real Real.semiring)
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                        (@Polynomial.{0} Real Real.semiring)
                                        (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                    (@Semiring.toModule.{0} Real Real.semiring)
                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                      (@Semiring.toModule.{0} Real Real.semiring)))
                                  Real (fun x => @Polynomial.{0} Real Real.semiring)
                                  (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real Real
                                    (@Polynomial.{0} Real Real.semiring) Real.semiring Real.semiring
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                        (@Polynomial.{0} Real Real.semiring)
                                        (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                    (@Semiring.toModule.{0} Real Real.semiring)
                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                      (@Semiring.toModule.{0} Real Real.semiring))
                                    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                  (@Polynomial.monomial.{0} Real Real.semiring i) a)
                                (@DFunLike.coe.{1, 1, 1}
                                  (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Real
                                    (@Polynomial.{0} Real Real.semiring)
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                        (@Polynomial.{0} Real Real.semiring)
                                        (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                    (@Semiring.toModule.{0} Real Real.semiring)
                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                      (@Semiring.toModule.{0} Real Real.semiring)))
                                  Real (fun x => @Polynomial.{0} Real Real.semiring)
                                  (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real Real
                                    (@Polynomial.{0} Real Real.semiring) Real.semiring Real.semiring
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                        (@Polynomial.{0} Real Real.semiring)
                                        (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                    (@Semiring.toModule.{0} Real Real.semiring)
                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                      (@Semiring.toModule.{0} Real Real.semiring))
                                    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                  (@Polynomial.monomial.{0} Real Real.semiring j) b))
                              (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.instAdd.{0} Real Real.semiring))
                                (@DFunLike.coe.{1, 1, 1}
                                  (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Real
                                    (@Polynomial.{0} Real Real.semiring)
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                        (@Polynomial.{0} Real Real.semiring)
                                        (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                    (@Semiring.toModule.{0} Real Real.semiring)
                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                      (@Semiring.toModule.{0} Real Real.semiring)))
                                  Real (fun x => @Polynomial.{0} Real Real.semiring)
                                  (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real Real
                                    (@Polynomial.{0} Real Real.semiring) Real.semiring Real.semiring
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                        (@Polynomial.{0} Real Real.semiring)
                                        (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                    (@Semiring.toModule.{0} Real Real.semiring)
                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                      (@Semiring.toModule.{0} Real Real.semiring))
                                    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                  (@Polynomial.monomial.{0} Real Real.semiring k) c)
                                (@DFunLike.coe.{1, 1, 1}
                                  (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) Real
                                    (@Polynomial.{0} Real Real.semiring)
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                        (@Polynomial.{0} Real Real.semiring)
                                        (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                    (@Semiring.toModule.{0} Real Real.semiring)
                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                      (@Semiring.toModule.{0} Real Real.semiring)))
                                  Real (fun x => @Polynomial.{0} Real Real.semiring)
                                  (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real Real
                                    (@Polynomial.{0} Real Real.semiring) Real.semiring Real.semiring
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                        (@Polynomial.{0} Real Real.semiring)
                                        (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                    (@Semiring.toModule.{0} Real Real.semiring)
                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                      (@Semiring.toModule.{0} Real Real.semiring))
                                    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                  (@Polynomial.monomial.{0} Real Real.semiring l) d)))) := @_root_.Couret.InterIA.Fibres.p2m_local_negacyclic_binomial_product_not_dvd

