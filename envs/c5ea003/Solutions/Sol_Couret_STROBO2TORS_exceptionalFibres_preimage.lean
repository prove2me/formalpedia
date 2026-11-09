-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalFibres_preimage
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:43:52.507545+00:00
-- url     : https://prove2.me/submissions/ca46264b-222f-4f34-ab01-ed12c52eedd1

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]



























theorem squareFibre_eq_of_orderedSquare_eq (S T : Finset G)
    (hsq : ∀ z : G, orderedSquare S z = orderedSquare T z) :
    squareFibre S = squareFibre T := by
  ext U
  rw [mem_squareFibre, mem_squareFibre]
  constructor
  · rintro ⟨hU, hSU⟩
    exact ⟨hU, fun z => (hsq z).symm.trans (hSU z)⟩
  · rintro ⟨hU, hTU⟩
    exact ⟨hU, fun z => (hsq z).trans (hTU z)⟩



/-- The preimage of an exceptional fibre under S ↦ its actual square fibre is that fibre. -/
theorem p2m_local_exceptionalFibres_preimage (F : Finset (Finset G))
    (hF : F ∈ (exceptionalFibres : Finset (Finset (Finset G)))) :
    exceptionalSupports.filter (fun S : Finset G => squareFibre S = F) = F := by
  obtain ⟨T, hT, htF⟩ := Finset.mem_image.mp hF
  have hcF : F.card = 2 * (twoTorsion : Finset G).card := by
    rw [← htF]; exact ((mem_exceptionalSupports_card T).mp hT).2
  ext S
  constructor
  · intro h
    obtain ⟨hS, hsF⟩ := Finset.mem_filter.mp h
    have hs3 := ((mem_exceptionalSupports_card S).mp hS).1
    rw [← hsF]
    exact (mem_squareFibre S S).mpr ⟨hs3, fun _ => rfl⟩
  · intro h
    have hST := h
    rw [← htF] at hST
    obtain ⟨hs3, hTS⟩ := (mem_squareFibre T S).mp hST
    have hsF : squareFibre S = F :=
      (squareFibre_eq_of_orderedSquare_eq T S hTS).symm.trans htF
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_exceptionalSupports_card S).mpr
      refine ⟨hs3, ?_⟩
      rw [hsF]; exact hcF
    · exact hsF

























































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (F : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
      (@Couret.STROBO2TORS.exceptionalFibres.{p2m_u_0} G inst inst_1 inst_2) F →
    @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} G)
        (fun S =>
          @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S) F)
        (fun a =>
          @Finset.decidableEq.{p2m_u_0} (Finset.{p2m_u_0} G) (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
            (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 a) F)
        (@Couret.STROBO2TORS.exceptionalSupports.{p2m_u_0} G inst inst_1 inst_2))
      F := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalFibres_preimage

