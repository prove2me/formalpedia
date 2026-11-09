-- Prove2me | solution 1 for Couret.CayleyDoublet.abelianThreeCospectral_of_parity
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:07:28.98806+00:00
-- url     : https://prove2.me/submissions/23623290-305e-4bae-8a98-814b894ebb86

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianCayleyMatrix_parity_sign
import Theorems.Thm_Couret_CayleyDoublet_abelianCayleyMatrix_sq_eq_of_quotient_order_three
import Theorems.Thm_Couret_CayleyDoublet_abelian_quotient_addOrderOf_three_iff
import Theorems.Thm_Couret_CayleySpectral_charpoly_eq_of_sq_eq_of_neg
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

/-- A sign symmetry gives invariance of the characteristic polynomial under negation. -/
theorem charpoly_neg_of_involution (A D : Matrix ι ι R)
    (hD : D * D = 1) (hA : D * A * D = -A) :
    (-A).charpoly = A.charpoly := by
  rw [← hA, Matrix.charpoly_mul_comm, ← mul_assoc, hD, one_mul]



/-- The two involutions may differ. Only the two matrix squares must agree. -/
theorem charpoly_eq_of_sq_eq_of_involutions [NoZeroDivisors R] (A B D E : Matrix ι ι R)
    (hsq : A ^ 2 = B ^ 2) (hD : D * D = 1) (hE : E * E = 1)
    (hA : D * A * D = -A) (hB : E * B * E = -B) :
    A.charpoly = B.charpoly :=
  charpoly_eq_of_sq_eq_of_neg A B hsq
    (charpoly_neg_of_involution A D hD hA)
    (charpoly_neg_of_involution B E hE hB)

/-- A bipartition is encoded by a sign at each index. -/
theorem diagonal_sign_involution (s : ι → R) (hs : ∀ i, s i * s i = 1) :
    diagonal s * diagonal s = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  simp only [hs, Matrix.diagonal_one]

theorem diagonal_sign_conj (A : Matrix ι ι R) (s : ι → R)
    (hs : ∀ i, s i * s i = 1)
    (hA : ∀ i j, A i j ≠ 0 → s i = -s j) :
    diagonal s * A * diagonal s = -A := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply]
  by_cases hz : A i j = 0
  · simp [hz]
  · rw [hA i j hz]
    calc
      -s j * A i j * s j = -(s j * s j) * A i j := by ring
      _ = -A i j := by rw [hs]; ring

theorem charpoly_eq_of_sq_eq_of_signs [NoZeroDivisors R] (A B : Matrix ι ι R)
    (s t : ι → R) (hs : ∀ i, s i * s i = 1) (ht : ∀ i, t i * t i = 1)
    (hA : ∀ i j, A i j ≠ 0 → s i = -s j)
    (hB : ∀ i j, B i j ≠ 0 → t i = -t j)
    (hsq : A ^ 2 = B ^ 2) : A.charpoly = B.charpoly :=
  charpoly_eq_of_sq_eq_of_involutions A B (diagonal s) (diagonal t) hsq
    (diagonal_sign_involution s hs) (diagonal_sign_involution t ht)
    (diagonal_sign_conj A s hs hA) (diagonal_sign_conj B t ht hB)





end Couret.CayleySpectral
namespace Couret.CayleySpectral
/-! An exact odd-power identity, valid in every unital associative ring. -/






















end Couret.CayleySpectral

namespace Couret.CayleyDoublet

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

















theorem abelianParitySign_sq (ε : G →+ ZMod 2) (x : G) :
    abelianParitySign ε x * abelianParitySign ε x = 1 := by
  simp only [abelianParitySign]
  split_ifs <;> norm_num



end Couret.CayleyDoublet

namespace Couret.CayleyDoublet
open Couret.CayleySpectral
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]








































end Couret.CayleyDoublet

namespace Couret.CayleyDoublet

open Classical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





/-- A supplied parity changes on every source and target arc. -/
theorem abelianThree_support_parity (a d h : G) (ε : G →+ ZMod 2)
    (ha : ε a = 1) (hd : ε d = 0) (hh : ε h = 0) :
    (∀ s ∈ AbelianSource a d h, ε s = 1) ∧
      (∀ s ∈ AbelianTarget a d h, ε s = 1) := by
  constructor
  · intro s hs
    simp only [AbelianSource, TripleSupport, Finset.mem_insert,
      Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;> simp [ha, hd, hh]
  · intro s hs
    simp only [AbelianTarget, TripleSupport, Finset.mem_insert,
      Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;> simp [ha, hd, hh]

/-- A parity killing h automatically kills d under the three-torsion premise. -/
theorem abelianThree_parity_d_zero (d h : G) (ε : G →+ ZMod 2)
    (hthree : (d + d) + d = 0 ∨ (d + d) + d = h) (hh : ε h = 0) :
    ε d = 0 := by
  have he : ε ((d + d) + d) = 0 := by
    rcases hthree with he | he <;> simp [he, hh]
  have ht : ε d + ε d = 0 := (by decide : ∀ x : ZMod 2, x + x = 0) (ε d)
  simpa only [map_add, ht, zero_add] using he

/-- Conditional spectral sufficiency for the actual finite directed graphs.
The parity is explicit; neither existence from quotient cardinality nor the
necessity of parity is assumed or asserted here. Its value at d is derived. -/
theorem p2m_local_abelianThreeCospectral_of_parity
    (a d h : G) (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (ε : G →+ ZMod 2) (ha : ε a = 1) (hh : ε h = 0) :
    (abelianCayleyMatrix (AbelianSource a d h)).charpoly =
      (abelianCayleyMatrix (AbelianTarget a d h)).charpoly := by
  have hd : ε d = 0 := abelianThree_parity_d_zero d h ε
    ((abelian_quotient_addOrderOf_three_iff d h hhalf).mp horder).1 hh
  obtain ⟨hS, hT⟩ := abelianThree_support_parity a d h ε ha hd hh
  exact Couret.CayleySpectral.charpoly_eq_of_sq_eq_of_signs _ _
    (abelianParitySign ε) (abelianParitySign ε)
    (abelianParitySign_sq ε) (abelianParitySign_sq ε)
    (abelianCayleyMatrix_parity_sign _ ε hS)
    (abelianCayleyMatrix_parity_sign _ ε hT)
    (abelianCayleyMatrix_sq_eq_of_quotient_order_three a d h hhalf hne horder)

















end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (a d h : G),
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
    @Ne.{p2m_u_0 + 1} G h
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Eq.{1} Nat
          (@addOrderOf.{p2m_u_0}
            (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
            (@SubNegMonoid.toAddMonoid.{p2m_u_0}
              (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
              (@AddGroup.toSubNegMonoid.{p2m_u_0}
                (@HasQuotient.Quotient.{p2m_u_0, p2m_u_0} G
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@QuotientAddGroup.instHasQuotientAddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h))
                (@QuotientAddGroup.Quotient.addGroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                  (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)
                  (@AddSubgroup.normal_of_isAddCommutative.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                    (@AddCommMagma.to_isCommutative.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst))))
                    (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h)))))
            (@QuotientAddGroup.mk.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
              (@AddSubgroup.zmultiples.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst) h) d))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        ∀
          (ε :
            @AddMonoidHom.{p2m_u_0, 0} G (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddZeroClass.toAddZero.{p2m_u_0} G
                (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
              (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddMonoidWithOne.toAddMonoid.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Field.toDivisionRing.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              Nat.fact_prime_two))))))))),
          @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                (@AddMonoidHom.{p2m_u_0, 0} G (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddZeroClass.toAddZero.{p2m_u_0} G
                    (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                  (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@AddMonoidWithOne.toAddMonoid.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@DivisionRing.toRing.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@Field.toDivisionRing.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  Nat.fact_prime_two)))))))))
                G (fun x => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddMonoidHom.instFunLike.{p2m_u_0, 0} G
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddZeroClass.toAddZero.{p2m_u_0} G
                    (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                  (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@AddMonoidWithOne.toAddMonoid.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@DivisionRing.toRing.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@Field.toDivisionRing.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  Nat.fact_prime_two)))))))))
                ε a)
              (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
                (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Field.toDivisionRing.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              Nat.fact_prime_two)))))))) →
            @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                  (@AddMonoidHom.{p2m_u_0, 0} G (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddZeroClass.toAddZero.{p2m_u_0} G
                      (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                    (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@AddMonoid.toAddZeroClass.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@AddMonoidWithOne.toAddMonoid.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@AddGroupWithOne.toAddMonoidWithOne.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Ring.toAddGroupWithOne.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@DivisionRing.toRing.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@Field.toDivisionRing.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    Nat.fact_prime_two)))))))))
                  G (fun x => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddMonoidHom.instFunLike.{p2m_u_0, 0} G
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddZeroClass.toAddZero.{p2m_u_0} G
                      (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                    (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@AddMonoid.toAddZeroClass.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@AddMonoidWithOne.toAddMonoid.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@AddGroupWithOne.toAddMonoidWithOne.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Ring.toAddGroupWithOne.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@DivisionRing.toRing.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@Field.toDivisionRing.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    Nat.fact_prime_two)))))))))
                  ε h)
                (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                  (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@instMulZeroClassOfSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@DivisionSemiring.toSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Semifield.toDivisionSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                Nat.fact_prime_two)))))))) →
              @Eq.{1}
                (@Polynomial.{0} Rat (@CommSemiring.toSemiring.{0} Rat (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))
                (@Matrix.charpoly.{0, p2m_u_0} Rat Rat.commRing G inst_1 inst_2
                  (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                    (@Couret.CayleyDoublet.AbelianSource.{p2m_u_0} G inst inst_1 a d h)))
                (@Matrix.charpoly.{0, p2m_u_0} Rat Rat.commRing G inst_1 inst_2
                  (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
                    (@Couret.CayleyDoublet.AbelianTarget.{p2m_u_0} G inst inst_1 a d h))) := @_root_.Couret.CayleyDoublet.p2m_local_abelianThreeCospectral_of_parity

