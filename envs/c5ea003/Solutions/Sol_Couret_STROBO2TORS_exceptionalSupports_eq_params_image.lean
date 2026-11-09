-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalSupports_eq_params_image
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:05:55.13342+00:00
-- url     : https://prove2.me/submissions/f9a9c108-8dc3-4641-8f5c-f13de196105e

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptional_difference_normalization
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalParams
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_mem_exceptionalSupports
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]



















theorem p2m_local_exceptionalSupports_eq_params_image :
    (exceptionalSupports : Finset (Finset G)) = exceptionalParams.image paramSupport := by
  ext S
  constructor
  · intro h
    obtain ⟨_, T, he⟩ := (mem_exceptionalSupports S).mp h
    obtain ⟨a, b, d, u, hd, hd0, hab, hu, h3, hs, ht⟩ := he
    obtain ⟨v, hv, hv0, hvS⟩ := exceptional_difference_normalization a b d hd hab h3
    exact Finset.mem_image.mpr ⟨((a, d), v),
      (mem_exceptionalParams a d v).mpr ⟨hd, hd0, hv, hv0⟩, (hs.trans hvS).symm⟩
  · intro h
    obtain ⟨⟨⟨a, d⟩, v⟩, hp, hs⟩ := Finset.mem_image.mp h
    obtain ⟨hd, hd0, hv, hv0⟩ := (mem_exceptionalParams a d v).mp hp
    rw [← hs]
    exact paramSupport_mem_exceptionalSupports a d v hd hd0 hv hv0





































































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
    (@Couret.STROBO2TORS.exceptionalSupports.{p2m_u_0} G inst inst_1 inst_2)
    (@Finset.image.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G) (Finset.{p2m_u_0} G)
      (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b) (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1)
      (@Couret.STROBO2TORS.exceptionalParams.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalSupports_eq_params_image

