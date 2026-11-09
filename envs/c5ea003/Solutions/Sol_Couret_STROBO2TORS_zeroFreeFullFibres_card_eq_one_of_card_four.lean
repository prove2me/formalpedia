-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_card_eq_one_of_card_four
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:48.850194+00:00
-- url     : https://prove2.me/submissions/b4b9e051-5320-49a8-83ac-5f27ce0c56be

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








/-- At order four there is only one triple avoiding zero, hence every
nonempty square-convolution fibre contains precisely that one triple. -/
theorem p2m_local_zeroFreeFullFibres_card_eq_one_of_card_four
    (hn : Fintype.card G = 4)
    (F : Finset (Finset G))
    (hF : F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G)))) :
    F.card = 1 := by
  have hUnique : ∀ S : Finset G, S.card = 3 → 0 ∉ S →
      S = (Finset.univ : Finset G).erase (0 : G) := by
    intro S hCard hZero
    have hSub : S ⊆ (Finset.univ : Finset G).erase (0 : G) := by
      intro x hx
      exact Finset.mem_erase.mpr
        ⟨(fun hx0 => hZero (hx0 ▸ hx)), Finset.mem_univ x⟩
    have hErase : ((Finset.univ : Finset G).erase (0 : G)).card = 3 := by
      simp [hn]
    exact Finset.eq_of_subset_of_card_le hSub (by omega)
  have hSub : F ⊆ ({(Finset.univ : Finset G).erase (0 : G)} :
      Finset (Finset G)) := by
    intro S hSF
    obtain ⟨hCard, hZero⟩ :=
      zeroFreeFullFibres_support_card_and_zero F hF S hSF
    simp [hUnique S hCard hZero]
  have hLe : F.card ≤ 1 := by
    calc
      F.card ≤ ({(Finset.univ : Finset G).erase (0 : G)} :
          Finset (Finset G)).card := Finset.card_le_card hSub
      _ = 1 := by simp
  have hPos : 0 < F.card :=
    Finset.card_pos.mpr (zeroFreeFullFibres_member_nonempty F hF)
  omega

end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat (@Fintype.card.{p2m_u_0} G inst_2) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    ∀ (F : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
      @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
            (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
          (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2) F →
        @Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) F)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_card_eq_one_of_card_four

