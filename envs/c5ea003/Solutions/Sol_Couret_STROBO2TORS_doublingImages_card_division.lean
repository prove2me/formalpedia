-- Prove2me | solution 1 for Couret.STROBO2TORS.doublingImages_card_division
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:18.895191+00:00
-- url     : https://prove2.me/submissions/2e2de86f-97d3-4030-a076-1da893d5b53b

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_group_card_eq_h_mul_doublingImages
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]













































theorem p2m_local_doublingImages_card_division :
    (doublingImages : Finset G).card = Fintype.card G / (twoTorsion : Finset G).card := by
  rw [group_card_eq_h_mul_doublingImages]
  exact (Nat.mul_div_cancel_left _ (twoTorsion_card_pos (G := G))).symm











































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.doublingImages.{p2m_u_0} G inst inst_1 inst_2))
    (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (@Fintype.card.{p2m_u_0} G inst_2)
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_doublingImages_card_division

