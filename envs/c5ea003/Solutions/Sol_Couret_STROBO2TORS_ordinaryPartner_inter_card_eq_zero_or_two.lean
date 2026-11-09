-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryPartner_inter_card_eq_zero_or_two
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:55:00.684987+00:00
-- url     : https://prove2.me/submissions/409c5df4-91ac-4850-b059-204ab757262c

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_inter_translateSupport_add_mem
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464

set_option autoImplicit false

/-!
Ordinary partners and the intersection of distinct three-element supports.

The intersection of a support with its translate by a two-torsion element
is stable under that translation. A nonzero translation therefore cannot
leave exactly one point in the intersection. For distinct three-element
supports, the intersection has cardinality zero or two.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



/-- Two distinct ordinary partners of cardinality three share either no
point or exactly two points. In particular, an ordinary partner cannot
have intersection of cardinality one with the original support. -/
theorem p2m_local_ordinaryPartner_inter_card_eq_zero_or_two
    (S T : Finset G) (hS : S.card = 3) (hT : T.card = 3)
    (hST : S ≠ T) (hOrd : OrdinaryPartner S T) :
    (S ∩ T).card = 0 ∨ (S ∩ T).card = 2 := by
  obtain ⟨u, hu, hTu⟩ := hOrd
  have hu0 : u ≠ 0 := by
    intro hz
    apply hST
    simpa [hz, translateSupport] using hTu.symm
  have hle : (S ∩ T).card ≤ 3 := by
    calc
      (S ∩ T).card ≤ S.card := Finset.card_le_card Finset.inter_subset_left
      _ = 3 := hS
  have hne1 : (S ∩ T).card ≠ 1 := by
    intro h1
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
    have hxmem : x ∈ S ∩ T := by rw [hx]; simp
    have hxumem : x + u ∈ S ∩ T := by
      rw [hTu] at hxmem ⊢
      exact inter_translateSupport_add_mem S u hu x hxmem
    have hxu : x + u = x := by
      simpa only [hx, Finset.mem_singleton] using hxumem
    apply hu0
    exact add_left_cancel (show x + u = x + 0 by simpa using hxu)
  have hne3 : (S ∩ T).card ≠ 3 := by
    intro h3
    have hIS : S ∩ T = S :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hIT : S ∩ T = T :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hST (hIS.symm.trans hIT)
  omega


end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (S T : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} Nat (@Finset.card.{p2m_u_0} G T) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      @Ne.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) S T →
        @Couret.STROBO2TORS.OrdinaryPartner.{p2m_u_0} G inst inst_1 S T →
          Or
            (@Eq.{1} Nat
              (@Finset.card.{p2m_u_0} G
                (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) S T))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Eq.{1} Nat
              (@Finset.card.{p2m_u_0} G
                (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) S T))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryPartner_inter_card_eq_zero_or_two

