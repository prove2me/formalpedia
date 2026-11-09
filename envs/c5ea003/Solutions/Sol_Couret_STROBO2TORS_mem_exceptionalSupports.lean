-- Prove2me | solution 1 for Couret.STROBO2TORS.mem_exceptionalSupports
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:17.678184+00:00
-- url     : https://prove2.me/submissions/de1b698c-5523-4dd9-8722-55e2061da0b5

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_two_h_iff_exception
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]













theorem p2m_local_mem_exceptionalSupports (S : Finset G) :
    S ∈ exceptionalSupports ↔ S.card = 3 ∧ ∃ T : Finset G, ExceptionalPartner S T := by
  simp only [exceptionalSupports, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_univ, true_and]
  constructor
  · rintro ⟨hS, hc⟩
    exact ⟨hS, (squareFibre_card_two_h_iff_exception S hS).mp hc⟩
  · rintro ⟨hS, he⟩
    exact ⟨hS, (squareFibre_card_two_h_iff_exception S hS).mpr he⟩











































































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  Iff
    (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
        (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@Couret.STROBO2TORS.exceptionalSupports.{p2m_u_0} G inst inst_1 inst_2) S)
    (And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun T =>
        @Couret.STROBO2TORS.ExceptionalPartner.{p2m_u_0} G inst inst_1 S T)) := @_root_.Couret.STROBO2TORS.p2m_local_mem_exceptionalSupports

