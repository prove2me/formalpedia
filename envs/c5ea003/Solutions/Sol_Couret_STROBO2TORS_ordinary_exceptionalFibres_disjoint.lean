-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinary_exceptionalFibres_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:38.861199+00:00
-- url     : https://prove2.me/submissions/239a0c45-7608-4870-a8d6-a49cbfcb71ca

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_member_card
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]















































































theorem p2m_local_ordinary_exceptionalFibres_disjoint :
    Disjoint (ordinaryFibres : Finset (Finset (Finset G))) exceptionalFibres := by
  apply Finset.disjoint_left.mpr
  intro F hO hE
  have ho := (Finset.mem_filter.mp hO).2
  have he := exceptionalFibres_member_card F hE
  have hp := twoTorsion_card_pos (G := G)
  omega









end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Disjoint.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
    (@Finset.partialOrder.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
    (@Finset.instOrderBot.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
    (@Couret.STROBO2TORS.ordinaryFibres.{p2m_u_0} G inst inst_1 inst_2)
    (@Couret.STROBO2TORS.exceptionalFibres.{p2m_u_0} G inst inst_1 inst_2) := @_root_.Couret.STROBO2TORS.p2m_local_ordinary_exceptionalFibres_disjoint

