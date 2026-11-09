-- Prove2me | solution 1 for Couret.STROBO2TORS.nontranslatedNeighbours_card_exceptional
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:16:29.777084+00:00
-- url     : https://prove2.me/submissions/1c84ba26-110a-467b-b0d5-c5ac96a9a09d

import Aesop
import Definitions.Def_Couret_Strobo2TorsNontranslationDegree_16ff2822736a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_subset_fibre
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Definitions.Def_Couret_Strobo2TorsNontranslationBridge_e18319b1ae30
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





/-- Every source triple has square-fibre size minus its ordinary orbit size
nontranslated partners. This is the first counting reduction. -/
theorem nontranslatedNeighbours_card (S : Finset G) (hS : S.card = 3) :
    (nontranslatedNeighbours S).card =
      (squareFibre S).card - (twoTorsion : Finset G).card := by
  rw [nontranslatedNeighbours,
    Finset.card_sdiff_of_subset (torsionOrbit_subset_fibre S hS),
    torsionOrbit_card S hS]

/-- Exceptional supports have exactly h exceptional partners. -/
theorem p2m_local_nontranslatedNeighbours_card_exceptional (S : Finset G)
    (hExc : S ∈ (exceptionalSupports : Finset (Finset G))) :
    (nontranslatedNeighbours S).card = (twoTorsion : Finset G).card := by
  obtain ⟨hS, hCard⟩ := (mem_exceptionalSupports_card S).mp hExc
  rw [nontranslatedNeighbours_card S hS, hCard]
  have hPos := twoTorsion_card_pos (G := G)
  omega









end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
        (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@Couret.STROBO2TORS.exceptionalSupports.{p2m_u_0} G inst inst_1 inst_2) S →
    @Eq.{1} Nat
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.nontranslatedNeighbours.{p2m_u_0} G inst inst_1 inst_2 S))
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_nontranslatedNeighbours_card_exceptional

