-- Prove2me | solution 1 for Couret.CayleyDoublet.abelianDoubletMatrix_sq_orderThree
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:45:26.149121+00:00
-- url     : https://prove2.me/submissions/009f4bfd-4381-43a0-b1b8-40c8e5d33182

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

















end Couret.CayleySpectral
namespace Couret.CayleySpectral
/-! An exact odd-power identity, valid in every unital associative ring. -/






















end Couret.CayleySpectral

namespace Couret.CayleyDoublet

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





theorem abelianTranslationMatrix_mul (s t : G) :
    abelianTranslationMatrix s * abelianTranslationMatrix t =
      abelianTranslationMatrix (s + t) := by
  ext x y
  simp only [abelianTranslationMatrix, Matrix.mul_apply, ite_mul, one_mul, zero_mul]
  simp [add_assoc]















end Couret.CayleyDoublet

namespace Couret.CayleyDoublet
open Couret.CayleySpectral
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]


theorem abelianDoubletMatrix_sq_halfTurn (d h : G) (hhalf : h + h = 0) :
    abelianDoubletMatrix d h ^ 2 = 2 * abelianDoubletMatrix (d + d) h := by
  have hcross₁ : d + (d + h) = (d + d) + h := by abel
  have hcross₂ : (d + h) + d = (d + d) + h := by abel
  have hsum : (d + h) + (d + h) = d + d := by
    calc
      (d + h) + (d + h) = (d + d) + (h + h) := by abel
      _ = d + d := by rw [hhalf, add_zero]
  simp only [abelianDoubletMatrix, sq, add_mul, mul_add,
    abelianTranslationMatrix_mul, hcross₁, hcross₂, hsum, two_mul]
  abel

theorem p2m_local_abelianDoubletMatrix_sq_orderThree (d h : G)
    (hhalf : h + h = 0)
    (hthree : (d + d) + d = 0 ∨ (d + d) + d = h) :
    abelianDoubletMatrix d h ^ 2 = 2 * abelianDoubletMatrix (-d) h := by
  rw [abelianDoubletMatrix_sq_halfTurn d h hhalf]
  congr 1
  rcases hthree with hthree | hthree
  · have hd : d + d = -d := by
      apply eq_neg_iff_add_eq_zero.mpr
      exact hthree
    rw [hd]
  · have hd : d + d = -d + h := by
      calc
        d + d = ((d + d) + d) - d := by abel
        _ = -d + h := by rw [hthree]; abel
    have hdh : (d + d) + h = -d := by
      calc
        (d + d) + h = -d + (h + h) := by rw [hd]; abel
        _ = -d := by rw [hhalf, add_zero]
    show abelianTranslationMatrix (d + d) + abelianTranslationMatrix ((d + d) + h) =
      abelianTranslationMatrix (-d) + abelianTranslationMatrix (-d + h)
    rw [hdh, hd, add_comm]



































end Couret.CayleyDoublet

namespace Couret.CayleyDoublet

open Classical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



























end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (d h : G),
  @Eq.{p2m_u_0 + 1} G
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        h h)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    Or
        (@Eq.{p2m_u_0 + 1} G
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              d d)
            d)
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
        (@Eq.{p2m_u_0 + 1} G
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              d d)
            d)
          h) →
      @Eq.{p2m_u_0 + 1} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
        (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
          (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
          (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) Nat
            (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
              (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
                (@Matrix.semiring.{0, p2m_u_0} G Rat Rat.semiring inst_2 inst_1))))
          (@Couret.CayleyDoublet.abelianDoubletMatrix.{p2m_u_0} G inst inst_1 d h)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
          (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
          (@instHMul.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
            (@Matrix.instMulOfFintypeOfAddCommMonoid.{0, p2m_u_0} G Rat inst_2 Rat.instMul Rat.addCommMonoid))
          (@OfNat.ofNat.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) (nat_lit 2)
            (@instOfNatAtLeastTwo.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat) (nat_lit 2)
              (@Matrix.instNatCastOfZero.{0, p2m_u_0} G Rat inst_1
                (@MulZeroClass.toZero.{0} Rat (@instMulZeroClassOfSemiring.{0} Rat Rat.semiring)) Rat.instNatCast)
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (@Couret.CayleyDoublet.abelianDoubletMatrix.{p2m_u_0} G inst inst_1
            (@Neg.neg.{p2m_u_0} G
              (@NegZeroClass.toNeg.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
              d)
            h)) := @_root_.Couret.CayleyDoublet.p2m_local_abelianDoubletMatrix_sq_orderThree

