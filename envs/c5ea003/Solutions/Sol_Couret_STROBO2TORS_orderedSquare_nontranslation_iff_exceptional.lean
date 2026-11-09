-- Prove2me | solution 1 for Couret.STROBO2TORS.orderedSquare_nontranslation_iff_exceptional
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:52:42.742411+00:00
-- url     : https://prove2.me/submissions/88a6aa45-f8ab-4ebd-afc0-aed7ea88cc4a

import Aesop
import Definitions.Def_Couret_Strobo2TorsNontranslationBridge_e18319b1ae30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Equal ordered squares without an ambient translation are exactly exceptional partners. -/
theorem p2m_local_orderedSquare_nontranslation_iff_exceptional
    (S T : Finset G) (hS : S.card = 3) (hT : T.card = 3) :
    ((∀ z : G, orderedSquare S z = orderedSquare T z) ∧
      ¬ ∃ v : G, T = translateSupport S v) ↔ ExceptionalPartner S T := by
  constructor
  · rintro ⟨hEq, hNoTranslate⟩
    rcases (orderedSquare_classification_iff S T hS hT).mp hEq with hOrd | hExc
    · obtain ⟨u, _, hu⟩ := hOrd
      exact False.elim (hNoTranslate ⟨u, hu⟩)
    · exact hExc
  · intro hExc
    exact ⟨(orderedSquare_classification_iff S T hS hT).mpr (Or.inr hExc),
      exceptionalPartner_not_any_translation S T hS hT hExc⟩



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
          (Not
            (@Exists.{p2m_u_0 + 1} G fun v =>
              @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) T
                (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S v))))
        (@Couret.STROBO2TORS.ExceptionalPartner.{p2m_u_0} G inst inst_1 S T) := @_root_.Couret.STROBO2TORS.p2m_local_orderedSquare_nontranslation_iff_exceptional

