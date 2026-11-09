-- Prove2me | solution 1 for Couret.CayleySpectral.two_colour_common_sq_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:44:26.059313+00:00
-- url     : https://prove2.me/submissions/fd3b2b25-5ec6-4f6d-ad1f-28638525f0eb

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






theorem p2m_local_two_colour_common_sq_mul_sub
    {R : Type*} [Ring R] (u v : R)
    (huv : Commute u v)
    (hu : u ^ 2 = 2 * v) (hv : v ^ 2 = 2 * u) :
    (1 + u) ^ 2 * ((1 + u) - (1 + v)) =
      (-3) * ((1 + u) - (1 + v)) := by
  have hexp : (1 + u) ^ 2 = 1 + 2 * u + 2 * v := by
    calc
      (1 + u) ^ 2 = 1 + 2 * u + u ^ 2 := by noncomm_ring
      _ = 1 + 2 * u + 2 * v := by rw [hu]
  calc
    (1 + u) ^ 2 * ((1 + u) - (1 + v)) =
        (u - v) + 2 * (u ^ 2 - v ^ 2) := by
      rw [hexp]
      noncomm_ring [huv.eq]
    _ = (-3) * ((1 + u) - (1 + v)) := by
      rw [hu, hv]
      noncomm_ring















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
theorem solution : ∀ {R : Type p2m_u_0} [inst : Ring.{p2m_u_0} R] (u v : R),
  @Commute.{p2m_u_0} R
      (@Distrib.toMul.{p2m_u_0} R (@instDistribOfSemiring.{p2m_u_0} R (@Ring.toSemiring.{p2m_u_0} R inst))) u v →
    @Eq.{p2m_u_0 + 1} R
        (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} R Nat R
          (@instHPow.{p2m_u_0, 0} R Nat
            (@Monoid.toPow.{p2m_u_0} R (@Semiring.toMonoid.{p2m_u_0} R (@Ring.toSemiring.{p2m_u_0} R inst))))
          u (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
          (@instHMul.{p2m_u_0} R
            (@Distrib.toMul.{p2m_u_0} R (@instDistribOfSemiring.{p2m_u_0} R (@Ring.toSemiring.{p2m_u_0} R inst))))
          (@OfNat.ofNat.{p2m_u_0} R (nat_lit 2)
            (@instOfNatAtLeastTwo.{p2m_u_0} R (nat_lit 2)
              (@AddMonoidWithOne.toNatCast.{p2m_u_0} R
                (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R (@Ring.toAddGroupWithOne.{p2m_u_0} R inst)))
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          v) →
      @Eq.{p2m_u_0 + 1} R
          (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} R Nat R
            (@instHPow.{p2m_u_0, 0} R Nat
              (@Monoid.toPow.{p2m_u_0} R (@Semiring.toMonoid.{p2m_u_0} R (@Ring.toSemiring.{p2m_u_0} R inst))))
            v (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
            (@instHMul.{p2m_u_0} R
              (@Distrib.toMul.{p2m_u_0} R (@instDistribOfSemiring.{p2m_u_0} R (@Ring.toSemiring.{p2m_u_0} R inst))))
            (@OfNat.ofNat.{p2m_u_0} R (nat_lit 2)
              (@instOfNatAtLeastTwo.{p2m_u_0} R (nat_lit 2)
                (@AddMonoidWithOne.toNatCast.{p2m_u_0} R
                  (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R (@Ring.toAddGroupWithOne.{p2m_u_0} R inst)))
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            u) →
        @Eq.{p2m_u_0 + 1} R
          (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
            (@instHMul.{p2m_u_0} R
              (@Distrib.toMul.{p2m_u_0} R (@instDistribOfSemiring.{p2m_u_0} R (@Ring.toSemiring.{p2m_u_0} R inst))))
            (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} R Nat R
              (@instHPow.{p2m_u_0, 0} R Nat
                (@Monoid.toPow.{p2m_u_0} R (@Semiring.toMonoid.{p2m_u_0} R (@Ring.toSemiring.{p2m_u_0} R inst))))
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
                (@instHAdd.{p2m_u_0} R
                  (@Distrib.toAdd.{p2m_u_0} R (@instDistribOfSemiring.{p2m_u_0} R (@Ring.toSemiring.{p2m_u_0} R inst))))
                (@OfNat.ofNat.{p2m_u_0} R (nat_lit 1)
                  (@One.toOfNat1.{p2m_u_0} R
                    (@AddMonoidWithOne.toOne.{p2m_u_0} R
                      (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R (@Ring.toAddGroupWithOne.{p2m_u_0} R inst)))))
                u)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
              (@instHSub.{p2m_u_0} R
                (@SubNegMonoid.toSub.{p2m_u_0} R
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} R
                    (@AddGroupWithOne.toAddGroup.{p2m_u_0} R (@Ring.toAddGroupWithOne.{p2m_u_0} R inst)))))
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
                (@instHAdd.{p2m_u_0} R
                  (@Distrib.toAdd.{p2m_u_0} R (@instDistribOfSemiring.{p2m_u_0} R (@Ring.toSemiring.{p2m_u_0} R inst))))
                (@OfNat.ofNat.{p2m_u_0} R (nat_lit 1)
                  (@One.toOfNat1.{p2m_u_0} R
                    (@AddMonoidWithOne.toOne.{p2m_u_0} R
                      (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R (@Ring.toAddGroupWithOne.{p2m_u_0} R inst)))))
                u)
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
                (@instHAdd.{p2m_u_0} R
                  (@Distrib.toAdd.{p2m_u_0} R (@instDistribOfSemiring.{p2m_u_0} R (@Ring.toSemiring.{p2m_u_0} R inst))))
                (@OfNat.ofNat.{p2m_u_0} R (nat_lit 1)
                  (@One.toOfNat1.{p2m_u_0} R
                    (@AddMonoidWithOne.toOne.{p2m_u_0} R
                      (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R (@Ring.toAddGroupWithOne.{p2m_u_0} R inst)))))
                v)))
          (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
            (@instHMul.{p2m_u_0} R
              (@Distrib.toMul.{p2m_u_0} R (@instDistribOfSemiring.{p2m_u_0} R (@Ring.toSemiring.{p2m_u_0} R inst))))
            (@Neg.neg.{p2m_u_0} R
              (@NegZeroClass.toNeg.{p2m_u_0} R
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} R
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} R
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} R
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} R
                        (@LieRing.toAddCommGroup.{p2m_u_0} R (@LieRing.ofAssociativeRing.{p2m_u_0} R inst)))))))
              (@OfNat.ofNat.{p2m_u_0} R (nat_lit 3)
                (@instOfNatAtLeastTwo.{p2m_u_0} R (nat_lit 3)
                  (@AddMonoidWithOne.toNatCast.{p2m_u_0} R
                    (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R (@Ring.toAddGroupWithOne.{p2m_u_0} R inst)))
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
            (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
              (@instHSub.{p2m_u_0} R
                (@SubNegMonoid.toSub.{p2m_u_0} R
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} R
                    (@AddGroupWithOne.toAddGroup.{p2m_u_0} R (@Ring.toAddGroupWithOne.{p2m_u_0} R inst)))))
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
                (@instHAdd.{p2m_u_0} R
                  (@Distrib.toAdd.{p2m_u_0} R (@instDistribOfSemiring.{p2m_u_0} R (@Ring.toSemiring.{p2m_u_0} R inst))))
                (@OfNat.ofNat.{p2m_u_0} R (nat_lit 1)
                  (@One.toOfNat1.{p2m_u_0} R
                    (@AddMonoidWithOne.toOne.{p2m_u_0} R
                      (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R (@Ring.toAddGroupWithOne.{p2m_u_0} R inst)))))
                u)
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
                (@instHAdd.{p2m_u_0} R
                  (@Distrib.toAdd.{p2m_u_0} R (@instDistribOfSemiring.{p2m_u_0} R (@Ring.toSemiring.{p2m_u_0} R inst))))
                (@OfNat.ofNat.{p2m_u_0} R (nat_lit 1)
                  (@One.toOfNat1.{p2m_u_0} R
                    (@AddMonoidWithOne.toOne.{p2m_u_0} R
                      (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R (@Ring.toAddGroupWithOne.{p2m_u_0} R inst)))))
                v))) := @_root_.Couret.CayleySpectral.p2m_local_two_colour_common_sq_mul_sub

