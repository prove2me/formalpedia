-- Prove2me | solution 1 for Couret.STROBO2TORS.orderedSquare_symmDiff_four_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:32.681043+00:00
-- url     : https://prove2.me/submissions/58335cf2-3409-4f13-825d-ad78ecad1c79

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryPartner_inter_card_eq_zero_or_two
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_card_balance
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





theorem triple_symmDiff_four_iff_inter_one
    (S T : Finset α) (hS : S.card = 3) (hT : T.card = 3) :
    (S ∆ T).card = 4 ↔ (S ∩ T).card = 1 := by
  have hbalance := triple_symmDiff_card_balance S T hS hT
  omega







end FiniteSets

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



/-- Delta four is precisely the exceptional branch with a common singleton. -/
theorem p2m_local_orderedSquare_symmDiff_four_iff
    (S T : Finset G) (hS : S.card = 3) (hT : T.card = 3) :
    ((∀ z, orderedSquare S z = orderedSquare T z) ∧ (S ∆ T).card = 4) ↔
      ExceptionalPartner S T ∧ (S ∩ T).card = 1 := by
  constructor
  · rintro ⟨hsq, hdelta⟩
    have hinter := (triple_symmDiff_four_iff_inter_one S T hS hT).mp hdelta
    have hST : S ≠ T := by
      intro heq
      subst T
      simp at hdelta
    rcases (orderedSquare_classification_iff S T hS hT).mp hsq with ho | he
    · have hcard := ordinaryPartner_inter_card_eq_zero_or_two S T hS hT hST ho
      omega
    · exact ⟨he, hinter⟩
  · rintro ⟨he, hinter⟩
    exact ⟨(orderedSquare_classification_iff S T hS hT).mpr (Or.inr he),
      (triple_symmDiff_four_iff_inter_one S T hS hT).mpr hinter⟩








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
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
        (And (@Couret.STROBO2TORS.ExceptionalPartner.{p2m_u_0} G inst inst_1 S T)
          (@Eq.{1} Nat
            (@Finset.card.{p2m_u_0} G
              (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) S T))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_orderedSquare_symmDiff_four_iff

