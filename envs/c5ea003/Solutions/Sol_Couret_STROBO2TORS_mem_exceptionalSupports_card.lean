-- Prove2me | solution 1 for Couret.STROBO2TORS.mem_exceptionalSupports_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:40.719115+00:00
-- url     : https://prove2.me/submissions/188e3c4d-eeaa-44c7-818b-a4099e2dbf15

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]

























theorem p2m_local_mem_exceptionalSupports_card (S : Finset G) :
    S ∈ exceptionalSupports ↔ S.card = 3 ∧
      (squareFibre S).card = 2 * (twoTorsion : Finset G).card := by
  simp [exceptionalSupports]































































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
      (@Eq.{1} Nat
        (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))) := @_root_.Couret.STROBO2TORS.p2m_local_mem_exceptionalSupports_card

