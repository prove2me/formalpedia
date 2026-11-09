-- Prove2me | solution 1 for Couret.InterIA.Fibres.modulus_coprime_monomial
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:59:42.799323+00:00
-- url     : https://prove2.me/submissions/3e6cdc3c-1e4f-4db1-a099-c09b46952ac9

import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Coprime.Basic

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial











theorem p2m_local_modulus_coprime_monomial (m : ℕ) (hm : 0 < m) (i : ℕ)
    (a : ℝ) (ha : a ≠ 0) : IsCoprime (X^m+1 : ℝ[X]) (monomial i a) := by
  have hx : IsCoprime (X^m+1 : ℝ[X]) X := by
    refine ⟨1,-(X^(m-1)),?_⟩
    have hp : (X : ℝ[X])^(m-1)*X=X^m := by
      rw [← pow_succ]; congr 1; omega
    simp only [one_mul,neg_mul,hp]
    simp [add_comm]
  have hpow : ∀ k : ℕ, IsCoprime (X^m+1 : ℝ[X]) (X^k) := by
    intro k
    induction k with
    | zero => exact ⟨0,1,by simp⟩
    | succ k ih => simpa only [pow_succ] using ih.mul_right hx
  have hc : IsCoprime (X^m+1 : ℝ[X]) (C a) := by
    refine ⟨0,C a⁻¹,?_⟩
    simp [← map_mul,ha]
  simpa only [C_mul_X_pow_eq_monomial] using hc.mul_right (hpow i)







end Couret.InterIA.Fibres

theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀ (i : Nat) (a : Real),
      @Ne.{1} Real a (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @IsCoprime.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.commSemiring.{0} Real Real.instCommSemiring)
          (@HAdd.hAdd.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.{0} Real Real.semiring)
            (@Polynomial.{0} Real Real.semiring)
            (@instHAdd.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instAdd.{0} Real Real.semiring))
            (@HPow.hPow.{0, 0, 0} (@Polynomial.{0} Real Real.semiring) Nat (@Polynomial.{0} Real Real.semiring)
              (@instHPow.{0, 0} (@Polynomial.{0} Real Real.semiring) Nat
                (@Monoid.toPow.{0} (@Polynomial.{0} Real Real.semiring)
                  (@Semiring.toMonoid.{0} (@Polynomial.{0} Real Real.semiring)
                    (@Polynomial.semiring.{0} Real Real.semiring))))
              (@Polynomial.X.{0} Real Real.semiring) m)
            (@OfNat.ofNat.{0} (@Polynomial.{0} Real Real.semiring) (nat_lit 1)
              (@One.toOfNat1.{0} (@Polynomial.{0} Real Real.semiring) (@Polynomial.instOne.{0} Real Real.semiring))))
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
            (@Polynomial.monomial.{0} Real Real.semiring i) a) := @_root_.Couret.InterIA.Fibres.p2m_local_modulus_coprime_monomial

