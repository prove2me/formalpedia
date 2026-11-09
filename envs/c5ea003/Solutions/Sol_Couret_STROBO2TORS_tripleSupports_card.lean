-- Prove2me | solution 1 for Couret.STROBO2TORS.tripleSupports_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:35.979202+00:00
-- url     : https://prove2.me/submissions/33ade4c1-771a-4d66-8831-aef9b84e3fca

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









































































theorem p2m_local_tripleSupports_card :
    (tripleSupports : Finset (Finset G)).card = (Fintype.card G).choose 3 := by
  simp [tripleSupports]















end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [AddCommGroup.{p2m_u_0} G] [DecidableEq.{p2m_u_0 + 1} G] [inst : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.tripleSupports.{p2m_u_0} G inst))
    (Nat.choose (@Fintype.card.{p2m_u_0} G inst) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) := @_root_.Couret.STROBO2TORS.p2m_local_tripleSupports_card

