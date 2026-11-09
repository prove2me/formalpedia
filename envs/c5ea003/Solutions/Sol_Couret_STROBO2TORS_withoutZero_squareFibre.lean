-- Prove2me | solution 1 for Couret.STROBO2TORS.withoutZero_squareFibre
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:25.308255+00:00
-- url     : https://prove2.me/submissions/d305bb1d-da4f-42d4-839b-9c137aabfee8

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]















theorem p2m_local_withoutZero_squareFibre (S : Finset G) : withoutZero (squareFibre S) = zeroFreeSquareFibre S := rfl































































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
    (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1
      (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S))
    (@Couret.STROBO2TORS.zeroFreeSquareFibre.{p2m_u_0} G inst inst_1 inst_2 S) := @_root_.Couret.STROBO2TORS.p2m_local_withoutZero_squareFibre

