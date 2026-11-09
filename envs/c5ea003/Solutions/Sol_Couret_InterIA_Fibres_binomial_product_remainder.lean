-- Prove2me | solution 1 for Couret.InterIA.Fibres.binomial_product_remainder
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:59:28.273583+00:00
-- url     : https://prove2.me/submissions/60961948-0ac2-4e8d-bac8-13dd02a891ef

import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_InterIA_Fibres_reducedProduct_degree_lt
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Coprime.Basic

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial







/-- The reduced polynomial is the actual monic remainder, not an assumed model. -/
theorem p2m_local_binomial_product_remainder (m r s : ℕ) (hr : r < m) (hs : s < m)
    (a b : ℝ) :
    ((1 + monomial r a) * (1 + monomial s b)) %ₘ (X^m + 1) =
      reducedProduct m r s a b := by
  have hm : 0 < m := by omega
  have hmonic : (X^m + 1 : ℝ[X]).Monic := by
    simpa using (monic_X_pow_add_C (R := ℝ) 1 hm.ne')
  have hdegree : (X^m + 1 : ℝ[X]).degree = (m : WithBot ℕ) := by
    simpa using degree_X_pow_add_C (R := ℝ) hm 1
  by_cases hsmall : r+s < m
  · apply (div_modByMonic_unique (0 : ℝ[X]) (reducedProduct m r s a b)
        hmonic ⟨?_,?_⟩).2
    · simp only [reducedProduct,hsmall,if_true,mul_zero,add_zero,
        ← C_mul_X_pow_eq_monomial,map_mul,pow_add]
      ring
    · rw [hdegree]
      exact reducedProduct_degree_lt m r s hr hs a b
  · apply (div_modByMonic_unique (monomial (r+s-m) (a*b))
        (reducedProduct m r s a b) hmonic ⟨?_,?_⟩).2
    · have he : m+(r+s-m)=r+s := by omega
      have hp : (X : ℝ[X])^m * X^(r+s-m) = X^(r+s) := by
        rw [← pow_add,he]
      simp only [reducedProduct,hsmall,if_false,← C_mul_X_pow_eq_monomial,map_neg,map_mul]
      calc
        _ = 1 + C a*X^r + C b*X^s + C a*C b*(X^m*X^(r+s-m)) := by ring
        _ = _ := by rw [hp,pow_add]; ring
    · rw [hdegree]
      exact reducedProduct_degree_lt m r s hr hs a b











end Couret.InterIA.Fibres

theorem solution : ∀ (m r s : Nat),
  @LT.lt.{0} Nat instLTNat r m →
    @LT.lt.{0} Nat instLTNat s m →
      ∀ (a b : Real),
        @Eq.{1} (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
          (@Polynomial.modByMonic.{0} Real Real.instRing
            (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
              (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
              (@instHMul.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instMul.{0} Real Real.semiring))
              (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                (@Polynomial.{0} Real Real.semiring)
                (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instAdd.{0} Real Real.semiring))
                (@OfNat.ofNat.{0} (@Polynomial.{0} Real Real.semiring) (nat_lit 1)
                  (@One.toOfNat1.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instOne.{0} Real Real.semiring)))
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
                  (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real Real (@Polynomial.{0} Real Real.semiring) Real.semiring
                    Real.semiring
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
                  (@Polynomial.monomial.{0} Real Real.semiring r) a))
              (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
                (@Polynomial.{0} Real Real.semiring)
                (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instAdd.{0} Real Real.semiring))
                (@OfNat.ofNat.{0} (@Polynomial.{0} Real Real.semiring) (nat_lit 1)
                  (@One.toOfNat1.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instOne.{0} Real Real.semiring)))
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
                  (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real Real (@Polynomial.{0} Real Real.semiring) Real.semiring
                    Real.semiring
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
                  (@Polynomial.monomial.{0} Real Real.semiring s) b)))
            (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
              (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
              (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
              (@instHAdd.{0} (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                (@Polynomial.instAdd.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)))
              (@HPow.hPow.{0, 0, 0} (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)) Nat
                (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                (@instHPow.{0, 0} (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)) Nat
                  (@Monoid.toPow.{0} (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                    (@Semiring.toMonoid.{0} (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                      (@Polynomial.semiring.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)))))
                (@Polynomial.X.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)) m)
              (@OfNat.ofNat.{0} (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing)) (nat_lit 1)
                (@One.toOfNat1.{0} (@Polynomial.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
                  (@Polynomial.instOne.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))))))
          (Couret.InterIA.Fibres.reducedProduct m r s a b) := @_root_.Couret.InterIA.Fibres.p2m_local_binomial_product_remainder

