-- Prove2me | solution 1 for Couret.InterIA.Fibres.ordered_negacyclic_binomial_product_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:05:31.437502+00:00
-- url     : https://prove2.me/submissions/044e508f-cebc-4bf2-a119-0ec61a3aaa0e

import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_InterIA_Fibres_binomial_product_remainder
import Theorems.Thm_Couret_InterIA_Fibres_modulus_coprime_monomial
import Theorems.Thm_Couret_InterIA_Fibres_reducedProduct_ne_zero
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Coprime.Basic

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial









/-- Actual nonvanishing modulo X^m+1 for normalised real binomials. -/
theorem normalised_negacyclic_binomial_product_ne_zero (m r s : ℕ)
    (hr0 : 0 < r) (hr : r < m) (hs0 : 0 < s) (hs : s < m)
    (a b : ℝ) (ha : a ≠ 0) :
    ((1 + monomial r a) * (1 + monomial s b)) %ₘ (X^m+1) ≠ 0 := by
  rw [binomial_product_remainder m r s hr hs]
  exact reducedProduct_ne_zero m r s hr0 hr hs0 hs a b ha



theorem binomial_factor (i j : ℕ) (hij : i ≤ j) (a b : ℝ) (ha : a ≠ 0) :
    monomial i a + monomial j b =
      monomial i a * (1+monomial (j-i) (b/a)) := by
  rw [mul_add,mul_one,monomial_mul_monomial]
  have he : i+(j-i)=j := by omega
  have hab : a*(b/a)=b := by
    rw [div_eq_mul_inv,mul_left_comm a b,mul_inv_cancel₀ ha,mul_one]
  rw [he,hab]

theorem p2m_local_ordered_negacyclic_binomial_product_not_dvd (m i j k l : ℕ)
    (hij : i < j) (hkl : k < l) (hj : j < m) (hl : l < m)
    (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ¬ (X^m+1 : ℝ[X]) ∣
      (monomial i a+monomial j b)*(monomial k c+monomial l d) := by
  intro hdiv
  have hm : 0 < m := by omega
  have hn := normalised_negacyclic_binomial_product_ne_zero m (j-i) (l-k)
    (by omega) (by omega) (by omega) (by omega) (b/a) (d/c) (div_ne_zero hb ha)
  have hmonic : (X^m+1 : ℝ[X]).Monic := by
    simpa using monic_X_pow_add_C (R := ℝ) 1 hm.ne'
  apply hn
  apply (modByMonic_eq_zero_iff_dvd hmonic).mpr
  have he : (monomial i a+monomial j b)*(monomial k c+monomial l d) =
      monomial (i+k) (a*c) *
      ((1+monomial (j-i) (b/a))*(1+monomial (l-k) (d/c))) := by
    rw [binomial_factor i j hij.le a b ha,binomial_factor k l hkl.le c d hc,
      ← monomial_mul_monomial]
    ring
  rw [he] at hdiv
  exact (modulus_coprime_monomial m hm (i+k) (a*c) (mul_ne_zero ha hc)).dvd_of_dvd_mul_left hdiv



end Couret.InterIA.Fibres

theorem solution : ∀ (m i j k l : Nat),
  @LT.lt.{0} Nat instLTNat i j →
    @LT.lt.{0} Nat instLTNat k l →
      @LT.lt.{0} Nat instLTNat j m →
        @LT.lt.{0} Nat instLTNat l m →
          ∀ (a b c d : Real),
            @Ne.{1} Real a (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
              @Ne.{1} Real b (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                @Ne.{1} Real c (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                  Not
                    (@Dvd.dvd.{0} (@Polynomial.{0} Real Real.semiring)
                      (@semigroupDvd.{0} (@Polynomial.{0} Real Real.semiring)
                        (@SemigroupWithZero.toSemigroup.{0} (@Polynomial.{0} Real Real.semiring)
                          (@NonUnitalSemiring.toSemigroupWithZero.{0} (@Polynomial.{0} Real Real.semiring)
                            (@NonUnitalCommSemiring.toNonUnitalSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                              (@NonUnitalCommRing.toNonUnitalCommSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                (@CommRing.toNonUnitalCommRing.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Polynomial.commRing.{0} Real Real.commRing)))))))
                      (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                        (@Polynomial.{0} Real Real.semiring)
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
                      (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                        (@Polynomial.{0} Real Real.semiring)
                        (@instHMul.{0} (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.instMul.{0} Real Real.semiring))
                        (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.{0} Real Real.semiring)
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
                                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                    (@Polynomial.semiring.{0} Real Real.semiring))))
                              (@Semiring.toModule.{0} Real Real.semiring)
                              (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                (@Semiring.toModule.{0} Real Real.semiring)))
                            Real (fun x => @Polynomial.{0} Real Real.semiring)
                            (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real Real (@Polynomial.{0} Real Real.semiring)
                              Real.semiring Real.semiring
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                  (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
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
                                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                    (@Polynomial.semiring.{0} Real Real.semiring))))
                              (@Semiring.toModule.{0} Real Real.semiring)
                              (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                (@Semiring.toModule.{0} Real Real.semiring)))
                            Real (fun x => @Polynomial.{0} Real Real.semiring)
                            (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real Real (@Polynomial.{0} Real Real.semiring)
                              Real.semiring Real.semiring
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                  (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                    (@Polynomial.semiring.{0} Real Real.semiring))))
                              (@Semiring.toModule.{0} Real Real.semiring)
                              (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                (@Semiring.toModule.{0} Real Real.semiring))
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                            (@Polynomial.monomial.{0} Real Real.semiring j) b))
                        (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                          (@Polynomial.{0} Real Real.semiring)
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
                                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                    (@Polynomial.semiring.{0} Real Real.semiring))))
                              (@Semiring.toModule.{0} Real Real.semiring)
                              (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                (@Semiring.toModule.{0} Real Real.semiring)))
                            Real (fun x => @Polynomial.{0} Real Real.semiring)
                            (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real Real (@Polynomial.{0} Real Real.semiring)
                              Real.semiring Real.semiring
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                  (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
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
                                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                    (@Polynomial.semiring.{0} Real Real.semiring))))
                              (@Semiring.toModule.{0} Real Real.semiring)
                              (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                (@Semiring.toModule.{0} Real Real.semiring)))
                            Real (fun x => @Polynomial.{0} Real Real.semiring)
                            (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real Real (@Polynomial.{0} Real Real.semiring)
                              Real.semiring Real.semiring
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                  (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                  (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                    (@Polynomial.semiring.{0} Real Real.semiring))))
                              (@Semiring.toModule.{0} Real Real.semiring)
                              (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                (@Semiring.toModule.{0} Real Real.semiring))
                              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                            (@Polynomial.monomial.{0} Real Real.semiring l) d)))) := @_root_.Couret.InterIA.Fibres.p2m_local_ordered_negacyclic_binomial_product_not_dvd

