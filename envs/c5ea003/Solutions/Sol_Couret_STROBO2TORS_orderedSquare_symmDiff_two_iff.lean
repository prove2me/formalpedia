-- Prove2me | solution 1 for Couret.STROBO2TORS.orderedSquare_symmDiff_two_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:16:35.414419+00:00
-- url     : https://prove2.me/submissions/a89db63f-4416-4f05-a2be-7aad9718d923

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalPartner_inter_card_ne_two
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_two_iff_inter_two
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

/-- Delta two is precisely the ordinary branch with two common elements. -/
theorem p2m_local_orderedSquare_symmDiff_two_iff
    (S T : Finset G) (hS : S.card = 3) (hT : T.card = 3) :
    ((∀ z, orderedSquare S z = orderedSquare T z) ∧ (S ∆ T).card = 2) ↔
      OrdinaryPartner S T ∧ (S ∩ T).card = 2 := by
  constructor
  · rintro ⟨hsq, hdelta⟩
    have hinter := (triple_symmDiff_two_iff_inter_two S T hS hT).mp hdelta
    rcases (orderedSquare_classification_iff S T hS hT).mp hsq with ho | he
    · exact ⟨ho, hinter⟩
    · exact (exceptionalPartner_inter_card_ne_two S T he hinter).elim
  · rintro ⟨ho, hinter⟩
    exact ⟨(orderedSquare_classification_iff S T hS hT).mpr (Or.inl ho),
      (triple_symmDiff_two_iff_inter_two S T hS hT).mpr hinter⟩










end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (S T : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} Nat (@Finset.card.{p2m_u_0} G T) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      Iff
        (And
          (∀ (z : G),
            @Eq.{1} Nat (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S z)
              (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 T z))
          (@Eq.{1} Nat
            (@Finset.card.{p2m_u_0} G
              (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                  (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instLattice.{p2m_u_0} G inst_1)))
                (@Finset.instSDiff.{p2m_u_0} G inst_1) S T))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (And (@Couret.STROBO2TORS.OrdinaryPartner.{p2m_u_0} G inst inst_1 S T)
          (@Eq.{1} Nat
            (@Finset.card.{p2m_u_0} G
              (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) S T))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := @_root_.Couret.STROBO2TORS.p2m_local_orderedSquare_symmDiff_two_iff

