-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_eq_empty_of_card_le_three
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:51.250207+00:00
-- url     : https://prove2.me/submissions/6b96a6a3-b7f7-4581-9767-cb7d4bd3a5df

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_support_card_and_zero
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

















/-- Every zero-free fibre listed by zeroFreeFullFibres is genuinely nonempty. -/
theorem zeroFreeFullFibres_member_nonempty
    (F : Finset (Finset G))
    (hF : F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G)))) :
    F.Nonempty := by
  change F ∈ (nonemptyFullFibres : Finset (Finset (Finset G))).image withoutZero at hF
  obtain ⟨K, hK, hKF⟩ := Finset.mem_image.mp hF
  have hKN : (withoutZero K).Nonempty := (Finset.mem_filter.mp hK).2
  rw [hKF] at hKN
  exact hKN







/-- No three-element support can avoid zero in groups of order at most 3. -/
theorem p2m_local_zeroFreeFullFibres_eq_empty_of_card_le_three
    (hn : Fintype.card G ≤ 3) :
    (zeroFreeFullFibres : Finset (Finset (Finset G))) = ∅ := by
  ext F
  constructor
  · intro hF
    obtain ⟨S, hS⟩ := zeroFreeFullFibres_member_nonempty F hF
    obtain ⟨hCard, hZero⟩ :=
      zeroFreeFullFibres_support_card_and_zero F hF S hS
    have hSub : S ⊆ (Finset.univ : Finset G).erase (0 : G) := by
      intro x hx
      apply Finset.mem_erase.mpr
      exact ⟨(fun hx0 => hZero (hx0 ▸ hx)), Finset.mem_univ x⟩
    have hErase : ((Finset.univ : Finset G).erase (0 : G)).card =
        Fintype.card G - 1 := by simp
    have hLe := Finset.card_le_card hSub
    omega
  · intro hF
    simp at hF


end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @LE.le.{0} Nat instLENat (@Fintype.card.{p2m_u_0} G inst_2)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2)
      (@EmptyCollection.emptyCollection.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (@Finset.instEmptyCollection.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_eq_empty_of_card_le_three

