-- Prove2me | solution 1 for Couret.CayleySpectral.trace_pow_eq_zero_of_odd_of_involution
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:21:09.834377+00:00
-- url     : https://prove2.me/submissions/3ec3e776-f61c-43f1-bd50-6f6c9d863a38

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













/-- The same sign symmetry kills every odd closed-walk trace. -/
theorem p2m_local_trace_pow_eq_zero_of_odd_of_involution (A D : Matrix ι ι ℚ)
    (hD : D * D = 1) (hA : D * A * D = -A) (n : ℕ) (hn : Odd n) :
    Matrix.trace (A ^ n) = 0 := by
  have hanti : SemiconjBy D A (-A) := by
    change D * A = -A * D
    calc
      D * A = (D * A * D) * D := by rw [mul_assoc, mul_assoc, hD, mul_one]
      _ = -A * D := by rw [hA]
  have hconj : D * A ^ n * D = (-A) ^ n := by
    rw [(hanti.pow_right n).eq, mul_assoc, hD, mul_one]
  have ht : Matrix.trace (A ^ n) = -Matrix.trace (A ^ n) := by
    calc
      Matrix.trace (A ^ n) = Matrix.trace (D * A ^ n * D) := by
        rw [Matrix.trace_mul_cycle, hD, one_mul]
      _ = -Matrix.trace (A ^ n) := by rw [hconj, hn.neg_pow, Matrix.trace_neg]
  exact eq_zero_of_neg_eq ht.symm



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


universe p2m_u_0
theorem solution : ∀ {ι : Type p2m_u_0} [inst : Fintype.{p2m_u_0} ι] [inst_1 : DecidableEq.{p2m_u_0 + 1} ι]
  (A D : Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat),
  @Eq.{p2m_u_0 + 1} (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat)
      (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat)
        (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat) (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat)
        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, p2m_u_0, p2m_u_0, p2m_u_0} ι ι ι Rat inst Rat.instMul
          Rat.addCommMonoid)
        D D)
      (@OfNat.ofNat.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat) (nat_lit 1)
        (@One.toOfNat1.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat)
          (@Matrix.one.{0, p2m_u_0} ι Rat inst_1
            (@MulZeroClass.toZero.{0} Rat (@instMulZeroClassOfSemiring.{0} Rat Rat.semiring))
            (@AddMonoidWithOne.toOne.{0} Rat
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Rat
                (@Ring.toAddGroupWithOne.{0} Rat
                  (@NormedRing.toRing.{0} Rat
                    (@NormedCommRing.toNormedRing.{0} Rat
                      (@NormedField.toNormedCommRing.{0} Rat Rat.instNormedField))))))))) →
    @Eq.{p2m_u_0 + 1} (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat)
        (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat)
          (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat) (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, p2m_u_0, p2m_u_0, p2m_u_0} ι ι ι Rat inst Rat.instMul
            Rat.addCommMonoid)
          (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat)
            (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat) (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, p2m_u_0, p2m_u_0, p2m_u_0} ι ι ι Rat inst Rat.instMul
              Rat.addCommMonoid)
            D A)
          D)
        (@Neg.neg.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat)
          (@Matrix.neg.{0, p2m_u_0, p2m_u_0} ι ι Rat Rat.instNeg) A) →
      ∀ (n : Nat),
        @Odd.{0} Nat Nat.instSemiring n →
          @Eq.{1} Rat
            (@Matrix.trace.{p2m_u_0, 0} ι Rat inst Rat.addCommMonoid
              (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat) Nat
                (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat)
                (@instHPow.{p2m_u_0, 0} (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat) Nat
                  (@Monoid.toPow.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat)
                    (@Semiring.toMonoid.{p2m_u_0} (Matrix.{p2m_u_0, p2m_u_0, 0} ι ι Rat)
                      (@Matrix.semiring.{0, p2m_u_0} ι Rat Rat.semiring inst inst_1))))
                A n))
            (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) := @_root_.Couret.CayleySpectral.p2m_local_trace_pow_eq_zero_of_odd_of_involution

