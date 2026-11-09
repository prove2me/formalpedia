-- Prove2me | solution 1 for Couret.CayleyDoublet.abelianCayleyMatrix_source_target_eq_translationTriple
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:32.970199+00:00
-- url     : https://prove2.me/submissions/14722eae-4e9a-4341-8375-5ab1635efa70

import Definitions.Def_Couret_CayleyTwoColourSpectral_cff7591a9c5d
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_abelianSixSeparations_of_double_ne
import Theorems.Thm_Couret_CayleyDoublet_abelian_quotient_addOrderOf_three_iff
import Theorems.Thm_Couret_CayleyDoublet_no_cross_collision_of_order_three
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











theorem abelianCayleyMatrix_eq_sum (S : Finset G) :
    abelianCayleyMatrix S = ∑ s ∈ S, abelianTranslationMatrix s := by
  ext x y
  have he (s : G) : y = x + s ↔ s = y - x := by
    constructor <;> intro h <;> rw [h] <;> abel
  simp [Matrix.sum_apply, abelianCayleyMatrix, abelianTranslationMatrix, he]









end Couret.CayleyDoublet

namespace Couret.CayleyDoublet
open Couret.CayleySpectral
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]








































end Couret.CayleyDoublet

namespace Couret.CayleyDoublet

open Classical

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]















/-- Finset adjacency agrees with the three translation sum when all three
increments are distinct. This is the required protection against multiplicities. -/
theorem abelianCayleyMatrix_triple (a b c : G)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    abelianCayleyMatrix ({a, b, c} : Finset G) =
      abelianTranslationMatrix a + abelianTranslationMatrix b +
        abelianTranslationMatrix c := by
  rw [abelianCayleyMatrix_eq_sum]
  have ha : a ∉ ({b, c} : Finset G) := by simp [hab, hac]
  have hb : b ∉ ({c} : Finset G) := by simp [hbc]
  rw [Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_singleton, add_assoc]

theorem p2m_local_abelianCayleyMatrix_source_target_eq_translationTriple
    (a d h : G) (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3) :
    abelianCayleyMatrix (AbelianSource a d h) = abelianTranslationTriple a d h ∧
      abelianCayleyMatrix (AbelianTarget a d h) = abelianTranslationTriple a (-d) h := by
  obtain ⟨hthree, hd0, hdh⟩ :=
    (abelian_quotient_addOrderOf_three_iff d h hhalf).mp horder
  obtain ⟨hd2, hdh2⟩ :=
    no_cross_collision_of_order_three d h hhalf hd0 hdh hthree
  obtain ⟨hs1, hs2, ht1, ht2, _, _⟩ :=
    abelianSixSeparations_of_double_ne a d h hhalf hd2 hdh2
  have hhsep (b : G) : b ≠ b + h := by
    intro he
    apply hne
    exact add_left_cancel (show b + h = b + 0 by simpa using he.symm)
  constructor
  · exact abelianCayleyMatrix_triple a (a + d) ((a + d) + h) hs1 hs2 (hhsep _)
  · simpa only [AbelianTarget, TripleSupport, abelianTranslationTriple, sub_eq_add_neg]
      using abelianCayleyMatrix_triple a (a - d) ((a - d) + h) ht1 ht2 (hhsep _)









end Couret.CayleyDoublet


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] [Fintype.{p2m_u_0} G]
  (a d h : G),
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
        And
          (@Eq.{p2m_u_0 + 1} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
            (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
              (@Couret.CayleyDoublet.AbelianSource.{p2m_u_0} G inst inst_1 a d h))
            (@Couret.CayleyDoublet.abelianTranslationTriple.{p2m_u_0} G inst inst_1 a d h))
          (@Eq.{p2m_u_0 + 1} (Matrix.{p2m_u_0, p2m_u_0, 0} G G Rat)
            (@Couret.CayleyDoublet.abelianCayleyMatrix.{p2m_u_0} G inst inst_1
              (@Couret.CayleyDoublet.AbelianTarget.{p2m_u_0} G inst inst_1 a d h))
            (@Couret.CayleyDoublet.abelianTranslationTriple.{p2m_u_0} G inst inst_1 a
              (@Neg.neg.{p2m_u_0} G
                (@NegZeroClass.toNeg.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))
                d)
              h)) := @_root_.Couret.CayleyDoublet.p2m_local_abelianCayleyMatrix_source_target_eq_translationTriple

