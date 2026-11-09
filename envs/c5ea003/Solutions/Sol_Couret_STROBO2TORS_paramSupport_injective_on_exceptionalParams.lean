-- Prove2me | solution 1 for Couret.STROBO2TORS.paramSupport_injective_on_exceptionalParams
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:44:42.974212+00:00
-- url     : https://prove2.me/submissions/f9525107-023c-4578-a88e-4f3121f28b54

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalParams
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_parameters_unique
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]





















theorem p2m_local_paramSupport_injective_on_exceptionalParams :
    Set.InjOn (paramSupport : (G × G) × G → Finset G)
      (exceptionalParams : Finset ((G × G) × G)) := by
  rintro ⟨⟨a, d⟩, v⟩ hp ⟨⟨t, e⟩, w⟩ hp' hs
  obtain ⟨hd, hd0, hv, hv0⟩ := (mem_exceptionalParams a d v).mp hp
  obtain ⟨he, he0, hw, hw0⟩ := (mem_exceptionalParams t e w).mp hp'
  obtain ⟨rfl, rfl, rfl⟩ := paramSupport_parameters_unique a d v t e w
    hd he hd0 he0 hv hw hv0 hw0 hs
  rfl



































































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Set.InjOn.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G) (Finset.{p2m_u_0} G)
    (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1)
    (@SetLike.coe.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G))
      (Prod.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G)
      (@Finset.instSetLike.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G))
      (@Couret.STROBO2TORS.exceptionalParams.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_paramSupport_injective_on_exceptionalParams

