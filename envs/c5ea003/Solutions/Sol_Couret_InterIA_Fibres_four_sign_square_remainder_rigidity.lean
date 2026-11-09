-- Prove2me | solution 1 for Couret.InterIA.Fibres.four_sign_square_remainder_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:49:40.156564+00:00
-- url     : https://prove2.me/submissions/194f8da2-8dd4-4350-bfbc-2c7a06ff16df

import Definitions.Def_Couret_FourSignRigidity_4bbe2289ca60
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_InterIA_Fibres_four_sign_square_rigidity
import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial















/-- The same rigidity from equality of the actual square remainders modulo X^m+1. -/
theorem p2m_local_four_sign_square_remainder_rigidity (m i j k l : ℕ)
    (hi : i < m) (hj : j < m) (hk : k < m) (hl : l < m)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (e0 e1 e2 e3 : Bool)
    (heq : ((monomial i a+monomial j b+monomial k c+monomial l d)^2) %ₘ (X^m+1) =
      ((signed e0 (monomial i a)+signed e1 (monomial j b)+
        signed e2 (monomial k c)+signed e3 (monomial l d))^2) %ₘ (X^m+1)) :
    signed e0 (monomial i a)+signed e1 (monomial j b)+
      signed e2 (monomial k c)+signed e3 (monomial l d) =
      monomial i a+monomial j b+monomial k c+monomial l d ∨
    signed e0 (monomial i a)+signed e1 (monomial j b)+
      signed e2 (monomial k c)+signed e3 (monomial l d) =
      -(monomial i a+monomial j b+monomial k c+monomial l d) := by
  apply four_sign_square_rigidity m i j k l hi hj hk hl hij hik hil hjk hjl hkl
    a b c d ha hb hc hd e0 e1 e2 e3
  have hm : 0 < m := by omega
  have hmonic : (X^m+1 : ℝ[X]).Monic := by
    simpa using monic_X_pow_add_C (R := ℝ) 1 hm.ne'
  apply (modByMonic_eq_zero_iff_dvd hmonic).mp
  rw [sub_modByMonic,heq,sub_self]

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
                                  @Eq.{1} (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                      (@Polynomial.modByMonic.{0} Real Real.instRing
                                        (@HPow.hPow.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                                          (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
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
                                        (@HAdd.hAdd.{0, 0, 0}
                                          (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                          (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                          (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                          (@instHAdd.{0}
                                            (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                            (@Polynomial.instAdd.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)))
                                          (@HPow.hPow.{0, 0, 0}
                                            (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)) Nat
                                            (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                            (@instHPow.{0, 0}
                                              (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)) Nat
                                              (@Monoid.toPow.{0}
                                                (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                                (@Semiring.toMonoid.{0}
                                                  (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                                  (@Polynomial.semiring.{0} Real
                                                    (@Ring.toSemiring.{0} Real Real.instRing)))))
                                            (@Polynomial.X.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)) m)
                                          (@OfNat.ofNat.{0}
                                            (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)) (nat_lit 1)
                                            (@One.toOfNat1.{0}
                                              (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                              (@Polynomial.instOne.{0} Real
                                                (@Ring.toSemiring.{0} Real Real.instRing))))))
                                      (@Polynomial.modByMonic.{0} Real Real.instRing
                                        (@HPow.hPow.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                                          (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
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
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (@HAdd.hAdd.{0, 0, 0}
                                          (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                          (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                          (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                          (@instHAdd.{0}
                                            (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                            (@Polynomial.instAdd.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)))
                                          (@HPow.hPow.{0, 0, 0}
                                            (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)) Nat
                                            (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                            (@instHPow.{0, 0}
                                              (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)) Nat
                                              (@Monoid.toPow.{0}
                                                (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                                (@Semiring.toMonoid.{0}
                                                  (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                                  (@Polynomial.semiring.{0} Real
                                                    (@Ring.toSemiring.{0} Real Real.instRing)))))
                                            (@Polynomial.X.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)) m)
                                          (@OfNat.ofNat.{0}
                                            (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)) (nat_lit 1)
                                            (@One.toOfNat1.{0}
                                              (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                                              (@Polynomial.instOne.{0} Real
                                                (@Ring.toSemiring.{0} Real Real.instRing)))))) →
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
                                              (@Polynomial.monomial.{0} Real Real.semiring l) d)))) := @_root_.Couret.InterIA.Fibres.p2m_local_four_sign_square_remainder_rigidity

