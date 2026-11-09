-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalPartner_inter_card_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:26.195197+00:00
-- url     : https://prove2.me/submissions/ad5d1fd7-d6ec-410f-8072-2df4eb6e61ad

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalPartner_normalized_inter
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464

set_option autoImplicit false

/-!
Intersection sizes for the exceptional branch of the triple-square
classification. The parameters below use the same coordinates as
ExceptionalPartner: the reflected doublet is based at b + b - a.
No finiteness assumption on the ambient abelian group is needed.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]













/-- Exceptional partners have an intersection of cardinality zero or one. -/
theorem exceptionalPartner_inter_card_zero_or_one (S T : Finset G)
    (he : ExceptionalPartner S T) :
    (S ∩ T).card = 0 ∨ (S ∩ T).card = 1 := by
  obtain ⟨a, b, d, u, hd, _, hab, hu, h3, hs, ht⟩ := he
  rw [hs, ht, exceptionalPartner_normalized_inter a b d u hd hab hu h3]
  by_cases hu0 : u = 0 <;> simp [hu0]

/-- An exceptional pair cannot share two support elements. -/
theorem p2m_local_exceptionalPartner_inter_card_ne_two (S T : Finset G)
    (he : ExceptionalPartner S T) : (S ∩ T).card ≠ 2 := by
  have hcard := exceptionalPartner_inter_card_zero_or_one S T he
  omega


end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (S T : Finset.{p2m_u_0} G),
  @Couret.STROBO2TORS.ExceptionalPartner.{p2m_u_0} G inst inst_1 S T →
    @Ne.{1} Nat
      (@Finset.card.{p2m_u_0} G
        (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) S T))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalPartner_inter_card_ne_two

