-- Prove2me | solution 1 for Couret.InterIA.Fibres.four_sign_square_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:10.049402+00:00
-- url     : https://prove2.me/submissions/de4fd724-0070-4572-a858-4153a84e27d4

import Definitions.Def_Couret_FourSignRigidity_4bbe2289ca60
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_InterIA_Fibres_four_partition_rigidity
import Theorems.Thm_Couret_InterIA_Fibres_modulus_coprime_monomial
import Theorems.Thm_Couret_InterIA_Fibres_negacyclic_binomial_product_not_dvd
import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial

theorem small_polynomial_not_dvd (m : ℕ) (hm : 0 < m) (p : ℝ[X])
    (hp : p.degree < (m : WithBot ℕ)) (hne : p ≠ 0) :
    ¬ (X^m+1 : ℝ[X]) ∣ p := by
  intro hd
  have hmonic : (X^m+1 : ℝ[X]).Monic := by
    simpa using monic_X_pow_add_C (R := ℝ) 1 hm.ne'
  have hdegree : (X^m+1 : ℝ[X]).degree = (m : WithBot ℕ) := by
    simpa using degree_X_pow_add_C (R := ℝ) hm 1
  have hz := (modByMonic_eq_zero_iff_dvd hmonic).mpr hd
  have hself := (modByMonic_eq_self_iff hmonic).mpr (hdegree.symm ▸ hp)
  rw [hself] at hz
  exact hne hz

theorem monomial_mul_small_not_dvd (m i : ℕ) (hm : 0 < m)
    (a : ℝ) (ha : a ≠ 0) (p : ℝ[X])
    (hp : p.degree < (m : WithBot ℕ)) (hne : p ≠ 0) :
    ¬ (X^m+1 : ℝ[X]) ∣ monomial i a * p := by
  intro hd
  exact small_polynomial_not_dvd m hm p hp hne
    ((modulus_coprime_monomial m hm i a ha).dvd_of_dvd_mul_left hd)

theorem trinomial_degree_lt (m i j k : ℕ) (hi : i < m) (hj : j < m)
    (hk : k < m) (a b c : ℝ) :
    (monomial i a + monomial j b + monomial k c).degree < (m : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro z hz
  have h1 : i ≠ z := by omega
  have h2 : j ≠ z := by omega
  have h3 : k ≠ z := by omega
  simp [coeff_monomial,h1,h2,h3]

theorem trinomial_ne_zero (i j k : ℕ) (hij : i ≠ j) (hik : i ≠ k)
    (a b c : ℝ) (ha : a ≠ 0) :
    monomial i a + monomial j b + monomial k c ≠ 0 := by
  intro hz
  have hc := congrArg (fun p : ℝ[X] => p.coeff i) hz
  simp [coeff_monomial,hij.symm,hik.symm] at hc
  exact ha hc





/-- Four distinct positions in the negacyclic fundamental interval have only a global sign ambiguity.
This theorem has no unproved nonvanishing premises: they are discharged above. -/
theorem p2m_local_four_sign_square_rigidity (m i j k l : ℕ)
    (hi : i < m) (hj : j < m) (hk : k < m) (hl : l < m)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (e0 e1 e2 e3 : Bool)
    (heq : (X^m+1 : ℝ[X]) ∣
      (monomial i a+monomial j b+monomial k c+monomial l d)^2 -
      (signed e0 (monomial i a)+signed e1 (monomial j b)+
       signed e2 (monomial k c)+signed e3 (monomial l d))^2) :
    signed e0 (monomial i a)+signed e1 (monomial j b)+
      signed e2 (monomial k c)+signed e3 (monomial l d) =
      monomial i a+monomial j b+monomial k c+monomial l d ∨
    signed e0 (monomial i a)+signed e1 (monomial j b)+
      signed e2 (monomial k c)+signed e3 (monomial l d) =
      -(monomial i a+monomial j b+monomial k c+monomial l d) := by
  have hm : 0 < m := by omega
  apply four_partition_rigidity (X^m+1) (monomial i a) (monomial j b)
    (monomial k c) (monomial l d) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e0 e1 e2 e3 heq
  · refine ⟨0,C (1/4 : ℝ),?_⟩
    change 0*(X^m+1)+C (1/4 : ℝ)*C (4 : ℝ)=1
    rw [zero_mul,zero_add,← map_mul]
    norm_num
  · exact monomial_mul_small_not_dvd m i hm a ha _
      (trinomial_degree_lt m j k l hj hk hl b c d)
      (trinomial_ne_zero j k l hjk hjl b c d hb)
  · exact monomial_mul_small_not_dvd m j hm b hb _
      (trinomial_degree_lt m i k l hi hk hl a c d)
      (trinomial_ne_zero i k l hik hil a c d ha)
  · exact monomial_mul_small_not_dvd m k hm c hc _
      (trinomial_degree_lt m i j l hi hj hl a b d)
      (trinomial_ne_zero i j l hij hil a b d ha)
  · exact monomial_mul_small_not_dvd m l hm d hd _
      (trinomial_degree_lt m i j k hi hj hk a b c)
      (trinomial_ne_zero i j k hij hik a b c ha)
  · exact negacyclic_binomial_product_not_dvd m i j k l hi hj hk hl hij hkl a b c d ha hb hc hd
  · exact negacyclic_binomial_product_not_dvd m i k j l hi hk hj hl hik hjl a c b d ha hc hb hd
  · exact negacyclic_binomial_product_not_dvd m i l j k hi hl hj hk hil hjk a d b c ha hd hb hc



end Couret.InterIA.Fibres

theorem solution : ∀ (m i j k l : Nat),
  @LT.lt.{0} Nat instLTNat i m →
    @LT.lt.{0} Nat instLTNat j m →
      @LT.lt.{0} Nat instLTNat k m →
        @LT.lt.{0} Nat instLTNat l m →
          @Ne.{1} Nat i j →
            @Ne.{1} Nat i k →
              @Ne.{1} Nat i l →
                @Ne.{1} Nat j k →
                  @Ne.{1} Nat j l →
                    @Ne.{1} Nat k l →
                      ∀ (a b c d : Real),
                        @Ne.{1} Real a (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                          @Ne.{1} Real b (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                            @Ne.{1} Real c (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                              @Ne.{1} Real d
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                                ∀ (e0 e1 e2 e3 : Bool),
                                  @Dvd.dvd.{0} (@Polynomial.{0} Real Real.semiring)
                                      (@semigroupDvd.{0} (@Polynomial.{0} Real Real.semiring)
                                        (@SemigroupWithZero.toSemigroup.{0} (@Polynomial.{0} Real Real.semiring)
                                          (@NonUnitalSemiring.toSemigroupWithZero.{0}
                                            (@Polynomial.{0} Real Real.semiring)
                                            (@NonUnitalCommSemiring.toNonUnitalSemiring.{0}
                                              (@Polynomial.{0} Real Real.semiring)
                                              (@NonUnitalCommRing.toNonUnitalCommSemiring.{0}
                                                (@Polynomial.{0} Real Real.semiring)
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
                                      (@HSub.hSub.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                        (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                        (@instHSub.{0} (@Polynomial.{0} Real Real.semiring)
                                          (@Polynomial.instSub.{0} Real Real.instRing))
                                        (@HPow.hPow.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                                          (@Polynomial.{0} Real Real.semiring)
                                          (@instHPow.{0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                                            (@Monoid.toPow.{0} (@Polynomial.{0} Real Real.semiring)
                                              (@Semiring.toMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                                (@Polynomial.semiring.{0} Real Real.semiring))))
                                          (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                            (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                            (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                              (@Polynomial.instAdd.{0} Real Real.semiring))
                                            (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                              (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                              (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                                (@Polynomial.instAdd.{0} Real Real.semiring))
                                              (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                                (@Polynomial.{0} Real Real.semiring)
                                                (@Polynomial.{0} Real Real.semiring)
                                                (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                                  (@Polynomial.instAdd.{0} Real Real.semiring))
                                                (@DFunLike.coe.{1, 1, 1}
                                                  (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                    Real (@Polynomial.{0} Real Real.semiring)
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
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
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
                                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                                    (@Semiring.toModule.{0} Real Real.semiring)
                                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                      (@Semiring.toModule.{0} Real Real.semiring))
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@Polynomial.monomial.{0} Real Real.semiring i) a)
                                                (@DFunLike.coe.{1, 1, 1}
                                                  (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                    Real (@Polynomial.{0} Real Real.semiring)
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
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
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
                                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                                    (@Semiring.toModule.{0} Real Real.semiring)
                                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                      (@Semiring.toModule.{0} Real Real.semiring))
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@Polynomial.monomial.{0} Real Real.semiring j) b))
                                              (@DFunLike.coe.{1, 1, 1}
                                                (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                  (@RingHom.id.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                  Real (@Polynomial.{0} Real Real.semiring)
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Semiring.toNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
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
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Semiring.toNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Polynomial.semiring.{0} Real Real.semiring))))
                                                  (@Semiring.toModule.{0} Real Real.semiring)
                                                  (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                    (@Semiring.toModule.{0} Real Real.semiring))
                                                  (@RingHom.id.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                (@Polynomial.monomial.{0} Real Real.semiring k) c))
                                            (@DFunLike.coe.{1, 1, 1}
                                              (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                (@RingHom.id.{0} Real
                                                  (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                Real (@Polynomial.{0} Real Real.semiring)
                                                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                  (@Polynomial.{0} Real Real.semiring)
                                                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@Semiring.toNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
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
                                                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                  (@Polynomial.{0} Real Real.semiring)
                                                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@Semiring.toNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Polynomial.semiring.{0} Real Real.semiring))))
                                                (@Semiring.toModule.{0} Real Real.semiring)
                                                (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                  (@Semiring.toModule.{0} Real Real.semiring))
                                                (@RingHom.id.{0} Real
                                                  (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                              (@Polynomial.monomial.{0} Real Real.semiring l) d))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (@HPow.hPow.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                                          (@Polynomial.{0} Real Real.semiring)
                                          (@instHPow.{0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                                            (@Monoid.toPow.{0} (@Polynomial.{0} Real Real.semiring)
                                              (@Semiring.toMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                                                (@Polynomial.semiring.{0} Real Real.semiring))))
                                          (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                            (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                            (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                              (@Polynomial.instAdd.{0} Real Real.semiring))
                                            (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                              (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                              (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                                (@Polynomial.instAdd.{0} Real Real.semiring))
                                              (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                                (@Polynomial.{0} Real Real.semiring)
                                                (@Polynomial.{0} Real Real.semiring)
                                                (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                                  (@Polynomial.instAdd.{0} Real Real.semiring))
                                                (Couret.InterIA.Fibres.signed e0
                                                  (@DFunLike.coe.{1, 1, 1}
                                                    (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                      (@RingHom.id.{0} Real
                                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                      Real (@Polynomial.{0} Real Real.semiring)
                                                      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                        (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                          (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
                                                          (@Semiring.toNonAssocSemiring.{0}
                                                            (@Polynomial.{0} Real Real.semiring)
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
                                                      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
                                                          (@Semiring.toNonAssocSemiring.{0}
                                                            (@Polynomial.{0} Real Real.semiring)
                                                            (@Polynomial.semiring.{0} Real Real.semiring))))
                                                      (@Semiring.toModule.{0} Real Real.semiring)
                                                      (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                        (@Semiring.toModule.{0} Real Real.semiring))
                                                      (@RingHom.id.{0} Real
                                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                    (@Polynomial.monomial.{0} Real Real.semiring i) a))
                                                (Couret.InterIA.Fibres.signed e1
                                                  (@DFunLike.coe.{1, 1, 1}
                                                    (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                      (@RingHom.id.{0} Real
                                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                      Real (@Polynomial.{0} Real Real.semiring)
                                                      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                        (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                          (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
                                                          (@Semiring.toNonAssocSemiring.{0}
                                                            (@Polynomial.{0} Real Real.semiring)
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
                                                      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
                                                          (@Semiring.toNonAssocSemiring.{0}
                                                            (@Polynomial.{0} Real Real.semiring)
                                                            (@Polynomial.semiring.{0} Real Real.semiring))))
                                                      (@Semiring.toModule.{0} Real Real.semiring)
                                                      (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                        (@Semiring.toModule.{0} Real Real.semiring))
                                                      (@RingHom.id.{0} Real
                                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                    (@Polynomial.monomial.{0} Real Real.semiring j) b)))
                                              (Couret.InterIA.Fibres.signed e2
                                                (@DFunLike.coe.{1, 1, 1}
                                                  (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                    Real (@Polynomial.{0} Real Real.semiring)
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
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
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
                                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                                    (@Semiring.toModule.{0} Real Real.semiring)
                                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                      (@Semiring.toModule.{0} Real Real.semiring))
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@Polynomial.monomial.{0} Real Real.semiring k) c)))
                                            (Couret.InterIA.Fibres.signed e3
                                              (@DFunLike.coe.{1, 1, 1}
                                                (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                  (@RingHom.id.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                  Real (@Polynomial.{0} Real Real.semiring)
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Semiring.toNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
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
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Semiring.toNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Polynomial.semiring.{0} Real Real.semiring))))
                                                  (@Semiring.toModule.{0} Real Real.semiring)
                                                  (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                    (@Semiring.toModule.{0} Real Real.semiring))
                                                  (@RingHom.id.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                (@Polynomial.monomial.{0} Real Real.semiring l) d)))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                                    Or
                                      (@Eq.{1} (@Polynomial.{0} Real Real.semiring)
                                        (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                          (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                          (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                            (@Polynomial.instAdd.{0} Real Real.semiring))
                                          (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                            (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                            (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                              (@Polynomial.instAdd.{0} Real Real.semiring))
                                            (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                              (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                              (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                                (@Polynomial.instAdd.{0} Real Real.semiring))
                                              (Couret.InterIA.Fibres.signed e0
                                                (@DFunLike.coe.{1, 1, 1}
                                                  (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                    Real (@Polynomial.{0} Real Real.semiring)
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
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
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
                                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                                    (@Semiring.toModule.{0} Real Real.semiring)
                                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                      (@Semiring.toModule.{0} Real Real.semiring))
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@Polynomial.monomial.{0} Real Real.semiring i) a))
                                              (Couret.InterIA.Fibres.signed e1
                                                (@DFunLike.coe.{1, 1, 1}
                                                  (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                    Real (@Polynomial.{0} Real Real.semiring)
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
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
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
                                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                                    (@Semiring.toModule.{0} Real Real.semiring)
                                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                      (@Semiring.toModule.{0} Real Real.semiring))
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@Polynomial.monomial.{0} Real Real.semiring j) b)))
                                            (Couret.InterIA.Fibres.signed e2
                                              (@DFunLike.coe.{1, 1, 1}
                                                (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                  (@RingHom.id.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                  Real (@Polynomial.{0} Real Real.semiring)
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Semiring.toNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
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
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Semiring.toNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Polynomial.semiring.{0} Real Real.semiring))))
                                                  (@Semiring.toModule.{0} Real Real.semiring)
                                                  (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                    (@Semiring.toModule.{0} Real Real.semiring))
                                                  (@RingHom.id.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                (@Polynomial.monomial.{0} Real Real.semiring k) c)))
                                          (Couret.InterIA.Fibres.signed e3
                                            (@DFunLike.coe.{1, 1, 1}
                                              (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                (@RingHom.id.{0} Real
                                                  (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                Real (@Polynomial.{0} Real Real.semiring)
                                                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                  (@Polynomial.{0} Real Real.semiring)
                                                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@Semiring.toNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
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
                                                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                  (@Polynomial.{0} Real Real.semiring)
                                                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@Semiring.toNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Polynomial.semiring.{0} Real Real.semiring))))
                                                (@Semiring.toModule.{0} Real Real.semiring)
                                                (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                  (@Semiring.toModule.{0} Real Real.semiring))
                                                (@RingHom.id.{0} Real
                                                  (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                              (@Polynomial.monomial.{0} Real Real.semiring l) d)))
                                        (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                          (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                          (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                            (@Polynomial.instAdd.{0} Real Real.semiring))
                                          (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                            (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                            (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                              (@Polynomial.instAdd.{0} Real Real.semiring))
                                            (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                              (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                              (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                                (@Polynomial.instAdd.{0} Real Real.semiring))
                                              (@DFunLike.coe.{1, 1, 1}
                                                (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                  (@RingHom.id.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                  Real (@Polynomial.{0} Real Real.semiring)
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Semiring.toNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
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
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Semiring.toNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Polynomial.semiring.{0} Real Real.semiring))))
                                                  (@Semiring.toModule.{0} Real Real.semiring)
                                                  (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                    (@Semiring.toModule.{0} Real Real.semiring))
                                                  (@RingHom.id.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                (@Polynomial.monomial.{0} Real Real.semiring i) a)
                                              (@DFunLike.coe.{1, 1, 1}
                                                (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                  (@RingHom.id.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                  Real (@Polynomial.{0} Real Real.semiring)
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Semiring.toNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
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
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Semiring.toNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Polynomial.semiring.{0} Real Real.semiring))))
                                                  (@Semiring.toModule.{0} Real Real.semiring)
                                                  (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                    (@Semiring.toModule.{0} Real Real.semiring))
                                                  (@RingHom.id.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                (@Polynomial.monomial.{0} Real Real.semiring j) b))
                                            (@DFunLike.coe.{1, 1, 1}
                                              (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                (@RingHom.id.{0} Real
                                                  (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                Real (@Polynomial.{0} Real Real.semiring)
                                                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                  (@Polynomial.{0} Real Real.semiring)
                                                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@Semiring.toNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
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
                                                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                  (@Polynomial.{0} Real Real.semiring)
                                                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@Semiring.toNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Polynomial.semiring.{0} Real Real.semiring))))
                                                (@Semiring.toModule.{0} Real Real.semiring)
                                                (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                  (@Semiring.toModule.{0} Real Real.semiring))
                                                (@RingHom.id.{0} Real
                                                  (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                              (@Polynomial.monomial.{0} Real Real.semiring k) c))
                                          (@DFunLike.coe.{1, 1, 1}
                                            (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                              (@RingHom.id.{0} Real
                                                (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                              Real (@Polynomial.{0} Real Real.semiring)
                                              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                  (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                (@Polynomial.{0} Real Real.semiring)
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
                                              (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                (@Polynomial.{0} Real Real.semiring)
                                                (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                  (@Polynomial.{0} Real Real.semiring)
                                                  (@Semiring.toNonAssocSemiring.{0} (@Polynomial.{0} Real Real.semiring)
                                                    (@Polynomial.semiring.{0} Real Real.semiring))))
                                              (@Semiring.toModule.{0} Real Real.semiring)
                                              (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                (@Semiring.toModule.{0} Real Real.semiring))
                                              (@RingHom.id.{0} Real
                                                (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                            (@Polynomial.monomial.{0} Real Real.semiring l) d)))
                                      (@Eq.{1} (@Polynomial.{0} Real Real.semiring)
                                        (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                          (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                          (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                            (@Polynomial.instAdd.{0} Real Real.semiring))
                                          (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                            (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                            (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                              (@Polynomial.instAdd.{0} Real Real.semiring))
                                            (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                              (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                              (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                                (@Polynomial.instAdd.{0} Real Real.semiring))
                                              (Couret.InterIA.Fibres.signed e0
                                                (@DFunLike.coe.{1, 1, 1}
                                                  (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                    Real (@Polynomial.{0} Real Real.semiring)
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
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
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
                                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                                    (@Semiring.toModule.{0} Real Real.semiring)
                                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                      (@Semiring.toModule.{0} Real Real.semiring))
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@Polynomial.monomial.{0} Real Real.semiring i) a))
                                              (Couret.InterIA.Fibres.signed e1
                                                (@DFunLike.coe.{1, 1, 1}
                                                  (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                    Real (@Polynomial.{0} Real Real.semiring)
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
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
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
                                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                                    (@Semiring.toModule.{0} Real Real.semiring)
                                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                      (@Semiring.toModule.{0} Real Real.semiring))
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@Polynomial.monomial.{0} Real Real.semiring j) b)))
                                            (Couret.InterIA.Fibres.signed e2
                                              (@DFunLike.coe.{1, 1, 1}
                                                (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                  (@RingHom.id.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                  Real (@Polynomial.{0} Real Real.semiring)
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Semiring.toNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
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
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Semiring.toNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Polynomial.semiring.{0} Real Real.semiring))))
                                                  (@Semiring.toModule.{0} Real Real.semiring)
                                                  (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                    (@Semiring.toModule.{0} Real Real.semiring))
                                                  (@RingHom.id.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                (@Polynomial.monomial.{0} Real Real.semiring k) c)))
                                          (Couret.InterIA.Fibres.signed e3
                                            (@DFunLike.coe.{1, 1, 1}
                                              (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                (@RingHom.id.{0} Real
                                                  (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                Real (@Polynomial.{0} Real Real.semiring)
                                                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                  (@Polynomial.{0} Real Real.semiring)
                                                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@Semiring.toNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
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
                                                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                  (@Polynomial.{0} Real Real.semiring)
                                                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@Semiring.toNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Polynomial.semiring.{0} Real Real.semiring))))
                                                (@Semiring.toModule.{0} Real Real.semiring)
                                                (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                  (@Semiring.toModule.{0} Real Real.semiring))
                                                (@RingHom.id.{0} Real
                                                  (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                              (@Polynomial.monomial.{0} Real Real.semiring l) d)))
                                        (@Neg.neg.{0} (@Polynomial.{0} Real Real.semiring)
                                          (@Polynomial.instNeg.{0} Real Real.instRing)
                                          (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                            (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                            (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                              (@Polynomial.instAdd.{0} Real Real.semiring))
                                            (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                              (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                                              (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                                (@Polynomial.instAdd.{0} Real Real.semiring))
                                              (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring)
                                                (@Polynomial.{0} Real Real.semiring)
                                                (@Polynomial.{0} Real Real.semiring)
                                                (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring)
                                                  (@Polynomial.instAdd.{0} Real Real.semiring))
                                                (@DFunLike.coe.{1, 1, 1}
                                                  (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                    Real (@Polynomial.{0} Real Real.semiring)
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
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
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
                                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                                    (@Semiring.toModule.{0} Real Real.semiring)
                                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                      (@Semiring.toModule.{0} Real Real.semiring))
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@Polynomial.monomial.{0} Real Real.semiring i) a)
                                                (@DFunLike.coe.{1, 1, 1}
                                                  (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                    Real (@Polynomial.{0} Real Real.semiring)
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                        (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
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
                                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Semiring.toNonAssocSemiring.{0}
                                                          (@Polynomial.{0} Real Real.semiring)
                                                          (@Polynomial.semiring.{0} Real Real.semiring))))
                                                    (@Semiring.toModule.{0} Real Real.semiring)
                                                    (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                      (@Semiring.toModule.{0} Real Real.semiring))
                                                    (@RingHom.id.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@Polynomial.monomial.{0} Real Real.semiring j) b))
                                              (@DFunLike.coe.{1, 1, 1}
                                                (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                  (@RingHom.id.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                  Real (@Polynomial.{0} Real Real.semiring)
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                      (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Semiring.toNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
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
                                                  (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Semiring.toNonAssocSemiring.{0}
                                                        (@Polynomial.{0} Real Real.semiring)
                                                        (@Polynomial.semiring.{0} Real Real.semiring))))
                                                  (@Semiring.toModule.{0} Real Real.semiring)
                                                  (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                    (@Semiring.toModule.{0} Real Real.semiring))
                                                  (@RingHom.id.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                (@Polynomial.monomial.{0} Real Real.semiring k) c))
                                            (@DFunLike.coe.{1, 1, 1}
                                              (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                                (@RingHom.id.{0} Real
                                                  (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                                Real (@Polynomial.{0} Real Real.semiring)
                                                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real
                                                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real
                                                    (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                  (@Polynomial.{0} Real Real.semiring)
                                                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@Semiring.toNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
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
                                                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0}
                                                  (@Polynomial.{0} Real Real.semiring)
                                                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0}
                                                    (@Polynomial.{0} Real Real.semiring)
                                                    (@Semiring.toNonAssocSemiring.{0}
                                                      (@Polynomial.{0} Real Real.semiring)
                                                      (@Polynomial.semiring.{0} Real Real.semiring))))
                                                (@Semiring.toModule.{0} Real Real.semiring)
                                                (@Polynomial.module.{0, 0} Real Real.semiring Real Real.semiring
                                                  (@Semiring.toModule.{0} Real Real.semiring))
                                                (@RingHom.id.{0} Real
                                                  (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                              (@Polynomial.monomial.{0} Real Real.semiring l) d)))) := @_root_.Couret.InterIA.Fibres.p2m_local_four_sign_square_rigidity

