-- Prove2me | solution 1 for Couret.CayleySpectral.charpoly_eq_of_sq_eq_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:57:24.757953+00:00
-- url     : https://prove2.me/submissions/95452020-e334-4d36-ae60-6ed4fcdb3ba9

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
import Definitions.Def_Couret_CayleyTwoColourAbelian_32e780a833c0

/-!
COU-20 — finite directed spectral bridge (17 October 2026).

This file connects finite-support convolution to the actual rational adjacency
matrices, proves cospectrality for a supplied additive parity and for the
already certified nongeneration branch, and proves exact odd-power and trace
difference formulas. Translation sums are identified with Finset adjacency
only after distinctness has been derived from the exact quotient order.

The construction of parity from quotient cardinality and the full spectral
classification are not asserted by these conditional spectral corollaries.
No undirected-graph extension, independent human review, release or priority
claim is made here. The preceding isomorphism dichotomy is imported unchanged.
-/

set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace Couret.CayleySpectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]



/-- Equal matrix squares and sign-symmetric characteristic polynomials imply equal
characteristic polynomials. This uses determinants, without eigenvalue approximations. -/
theorem p2m_local_charpoly_eq_of_sq_eq_of_neg [NoZeroDivisors R] (A B : Matrix ι ι R)
    (hsq : A ^ 2 = B ^ 2)
    (hA : (-A).charpoly = A.charpoly)
    (hB : (-B).charpoly = B.charpoly) :
    A.charpoly = B.charpoly := by
  have hm : A.charmatrix * (-A).charmatrix =
      B.charmatrix * (-B).charmatrix := by
    apply matPolyEquiv.injective
    simp only [map_mul, Matrix.matPolyEquiv_charmatrix, map_neg, sub_neg_eq_add]
    rw [← (Polynomial.commute_X (C A)).mul_self_sub_mul_self_eq',
      ← (Polynomial.commute_X (C B)).mul_self_sub_mul_self_eq']
    simpa only [← pow_two, map_pow] using
      congrArg (fun M : Matrix ι ι R => (X : (Matrix ι ι R)[X]) ^ 2 - C M) hsq
  have hp : A.charpoly ^ 2 = B.charpoly ^ 2 := by
    have hd := congrArg Matrix.det hm
    simp only [Matrix.det_mul] at hd
    change A.charpoly * (-A).charpoly = B.charpoly * (-B).charpoly at hd
    simpa only [hA, hB, pow_two] using hd
  rcases (eq_or_eq_neg_of_sq_eq_sq _ _ hp) with h | h
  · exact h
  · have hh := congrArg Polynomial.leadingCoeff h
    rw [Polynomial.leadingCoeff_neg, A.charpoly_monic.leadingCoeff,
      B.charpoly_monic.leadingCoeff] at hh
    calc
      A.charpoly = -B.charpoly := h
      _ = (-1 : R) • B.charpoly := (neg_one_smul R _).symm
      _ = (1 : R) • B.charpoly := by rw [← hh]
      _ = B.charpoly := one_smul _ _













end Couret.CayleySpectral
namespace Couret.CayleySpectral
/-! An exact odd-power identity, valid in every unital associative ring. -/






















end Couret.CayleySpectral

namespace Couret.CayleyDoublet

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





















end Couret.CayleyDoublet

namespace Couret.CayleyDoublet
open Couret.CayleySpectral
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]








































end Couret.CayleyDoublet

namespace Couret.CayleyDoublet

open Classical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



























end Couret.CayleyDoublet


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {ι : Type p2m_u_0} [inst : Fintype.{p2m_u_0} ι] [inst_1 : DecidableEq.{p2m_u_0 + 1} ι] {R : Type p2m_u_1}
  [inst_2 : CommRing.{p2m_u_1} R]
  [@NoZeroDivisors.{p2m_u_1} R
      (@Distrib.toMul.{p2m_u_1} R
        (@instDistribOfSemiring.{p2m_u_1} R
          (@CommSemiring.toSemiring.{p2m_u_1} R (@CommRing.toCommSemiring.{p2m_u_1} R inst_2))))
      (@MulZeroClass.toZero.{p2m_u_1} R
        (@instMulZeroClassOfSemiring.{p2m_u_1} R
          (@CommSemiring.toSemiring.{p2m_u_1} R (@CommRing.toCommSemiring.{p2m_u_1} R inst_2))))]
  (A B : Matrix.{p2m_u_0, p2m_u_0, p2m_u_1} ι ι R),
  @Eq.{(max p2m_u_0 p2m_u_1) + 1} (Matrix.{p2m_u_0, p2m_u_0, p2m_u_1} ι ι R)
      (@HPow.hPow.{max p2m_u_0 p2m_u_1, 0, max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_0, p2m_u_0, p2m_u_1} ι ι R) Nat
        (Matrix.{p2m_u_0, p2m_u_0, p2m_u_1} ι ι R)
        (@instHPow.{max p2m_u_0 p2m_u_1, 0} (Matrix.{p2m_u_0, p2m_u_0, p2m_u_1} ι ι R) Nat
          (@Monoid.toPow.{max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_0, p2m_u_0, p2m_u_1} ι ι R)
            (@Semiring.toMonoid.{max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_0, p2m_u_0, p2m_u_1} ι ι R)
              (@Matrix.semiring.{p2m_u_1, p2m_u_0} ι R
                (@CommSemiring.toSemiring.{p2m_u_1} R (@CommRing.toCommSemiring.{p2m_u_1} R inst_2)) inst inst_1))))
        A (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HPow.hPow.{max p2m_u_0 p2m_u_1, 0, max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_0, p2m_u_0, p2m_u_1} ι ι R) Nat
        (Matrix.{p2m_u_0, p2m_u_0, p2m_u_1} ι ι R)
        (@instHPow.{max p2m_u_0 p2m_u_1, 0} (Matrix.{p2m_u_0, p2m_u_0, p2m_u_1} ι ι R) Nat
          (@Monoid.toPow.{max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_0, p2m_u_0, p2m_u_1} ι ι R)
            (@Semiring.toMonoid.{max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_0, p2m_u_0, p2m_u_1} ι ι R)
              (@Matrix.semiring.{p2m_u_1, p2m_u_0} ι R
                (@CommSemiring.toSemiring.{p2m_u_1} R (@CommRing.toCommSemiring.{p2m_u_1} R inst_2)) inst inst_1))))
        B (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
    @Eq.{p2m_u_1 + 1}
        (@Polynomial.{p2m_u_1} R (@CommSemiring.toSemiring.{p2m_u_1} R (@CommRing.toCommSemiring.{p2m_u_1} R inst_2)))
        (@Matrix.charpoly.{p2m_u_1, p2m_u_0} R inst_2 ι inst_1 inst
          (@Neg.neg.{max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_0, p2m_u_0, p2m_u_1} ι ι R)
            (@Matrix.neg.{p2m_u_1, p2m_u_0, p2m_u_0} ι ι R
              (@NegZeroClass.toNeg.{p2m_u_1} R
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_1} R
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_1} R
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_1} R
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_1} R
                        (@LieRing.toAddCommGroup.{p2m_u_1} R
                          (@LieRing.ofAssociativeRing.{p2m_u_1} R (@CommRing.toRing.{p2m_u_1} R inst_2)))))))))
            A))
        (@Matrix.charpoly.{p2m_u_1, p2m_u_0} R inst_2 ι inst_1 inst A) →
      @Eq.{p2m_u_1 + 1}
          (@Polynomial.{p2m_u_1} R (@CommSemiring.toSemiring.{p2m_u_1} R (@CommRing.toCommSemiring.{p2m_u_1} R inst_2)))
          (@Matrix.charpoly.{p2m_u_1, p2m_u_0} R inst_2 ι inst_1 inst
            (@Neg.neg.{max p2m_u_0 p2m_u_1} (Matrix.{p2m_u_0, p2m_u_0, p2m_u_1} ι ι R)
              (@Matrix.neg.{p2m_u_1, p2m_u_0, p2m_u_0} ι ι R
                (@NegZeroClass.toNeg.{p2m_u_1} R
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_1} R
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_1} R
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_1} R
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_1} R
                          (@LieRing.toAddCommGroup.{p2m_u_1} R
                            (@LieRing.ofAssociativeRing.{p2m_u_1} R (@CommRing.toRing.{p2m_u_1} R inst_2)))))))))
              B))
          (@Matrix.charpoly.{p2m_u_1, p2m_u_0} R inst_2 ι inst_1 inst B) →
        @Eq.{p2m_u_1 + 1}
          (@Polynomial.{p2m_u_1} R (@CommSemiring.toSemiring.{p2m_u_1} R (@CommRing.toCommSemiring.{p2m_u_1} R inst_2)))
          (@Matrix.charpoly.{p2m_u_1, p2m_u_0} R inst_2 ι inst_1 inst A)
          (@Matrix.charpoly.{p2m_u_1, p2m_u_0} R inst_2 ι inst_1 inst B) := @_root_.Couret.CayleySpectral.p2m_local_charpoly_eq_of_sq_eq_of_neg

