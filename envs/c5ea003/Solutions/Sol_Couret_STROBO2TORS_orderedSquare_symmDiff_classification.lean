-- Prove2me | solution 1 for Couret.STROBO2TORS.orderedSquare_symmDiff_classification
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:52:47.014379+00:00
-- url     : https://prove2.me/submissions/f51425b9-e243-4dfc-a408-8641d25d2fc8

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_orderedSquare_symmDiff_four_iff
import Theorems.Thm_Couret_STROBO2TORS_orderedSquare_symmDiff_two_iff
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_card_cases
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.SymmDiff

set_option autoImplicit false

/-!
Refinement of the ordered-square classification by symmetric-difference
cardinality. The supports have cardinality three; zero is permitted.
The ambient abelian group need not be finite.
This module classifies the delta=2,4,6 cases; it does not count their pairs.
-/

open scoped symmDiff

namespace Couret.STROBO2TORS

section FiniteSets

variable {α : Type*} [DecidableEq α]













end FiniteSets

variable {G : Type*} [AddCommGroup G] [DecidableEq G]







/-- Complete delta=2,4,6 subdivision for distinct triple supports. -/
theorem p2m_local_orderedSquare_symmDiff_classification
    (S T : Finset G) (hS : S.card = 3) (hT : T.card = 3) (hST : S ≠ T) :
    (∀ z, orderedSquare S z = orderedSquare T z) ↔
      ((S ∆ T).card = 2 ∧ OrdinaryPartner S T) ∨
      ((S ∆ T).card = 4 ∧ ExceptionalPartner S T) ∨
      ((S ∆ T).card = 6 ∧ (OrdinaryPartner S T ∨ ExceptionalPartner S T)) := by
  constructor
  · intro hsq
    rcases triple_symmDiff_card_cases S T hS hT hST with htwo | hfour | hsix
    · exact Or.inl ⟨htwo, ((orderedSquare_symmDiff_two_iff S T hS hT).mp
        ⟨hsq, htwo⟩).1⟩
    · exact Or.inr (Or.inl ⟨hfour, ((orderedSquare_symmDiff_four_iff S T hS hT).mp
        ⟨hsq, hfour⟩).1⟩)
    · exact Or.inr (Or.inr ⟨hsix,
        (orderedSquare_classification_iff S T hS hT).mp hsq⟩)
  · intro h
    rcases h with ⟨_, ho⟩ | ⟨_, he⟩ | ⟨_, hbranch⟩
    · exact (orderedSquare_classification_iff S T hS hT).mpr (Or.inl ho)
    · exact (orderedSquare_classification_iff S T hS hT).mpr (Or.inr he)
    · exact (orderedSquare_classification_iff S T hS hT).mpr hbranch




end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (S T : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} Nat (@Finset.card.{p2m_u_0} G T) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      @Ne.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) S T →
        Iff
          (∀ (z : G),
            @Eq.{1} Nat (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S z)
              (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 T z))
          (Or
            (And
              (@Eq.{1} Nat
                (@Finset.card.{p2m_u_0} G
                  (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                    (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                      (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G)
                        (@Finset.instLattice.{p2m_u_0} G inst_1)))
                    (@Finset.instSDiff.{p2m_u_0} G inst_1) S T))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Couret.STROBO2TORS.OrdinaryPartner.{p2m_u_0} G inst inst_1 S T))
            (Or
              (And
                (@Eq.{1} Nat
                  (@Finset.card.{p2m_u_0} G
                    (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                      (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                        (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G)
                          (@Finset.instLattice.{p2m_u_0} G inst_1)))
                      (@Finset.instSDiff.{p2m_u_0} G inst_1) S T))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@Couret.STROBO2TORS.ExceptionalPartner.{p2m_u_0} G inst inst_1 S T))
              (And
                (@Eq.{1} Nat
                  (@Finset.card.{p2m_u_0} G
                    (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                      (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                        (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G)
                          (@Finset.instLattice.{p2m_u_0} G inst_1)))
                      (@Finset.instSDiff.{p2m_u_0} G inst_1) S T))
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                (Or (@Couret.STROBO2TORS.OrdinaryPartner.{p2m_u_0} G inst inst_1 S T)
                  (@Couret.STROBO2TORS.ExceptionalPartner.{p2m_u_0} G inst inst_1 S T))))) := @_root_.Couret.STROBO2TORS.p2m_local_orderedSquare_symmDiff_classification

