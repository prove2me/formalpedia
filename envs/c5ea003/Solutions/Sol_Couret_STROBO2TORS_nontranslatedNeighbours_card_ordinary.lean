-- Prove2me | solution 1 for Couret.STROBO2TORS.nontranslatedNeighbours_card_ordinary
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:29.379342+00:00
-- url     : https://prove2.me/submissions/4955dc2f-4b34-459d-bf34-257d9fecceb0

import Aesop
import Definitions.Def_Couret_Strobo2TorsNontranslationDegree_16ff2822736a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_h_or_two_h
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_subset_fibre
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



/-- An ordinary support has no nontranslated partners. -/
theorem p2m_local_nontranslatedNeighbours_card_ordinary (S : Finset G)
    (hS : S.card = 3)
    (hNotExc : S ∉ (exceptionalSupports : Finset (Finset G))) :
    (nontranslatedNeighbours S).card = 0 := by
  rcases squareFibre_card_h_or_two_h S hS with hOrd | hExc
  · rw [nontranslatedNeighbours_card S hS, hOrd, Nat.sub_self]
  · exact (hNotExc ((mem_exceptionalSupports_card S).mpr ⟨hS, hExc⟩)).elim







end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    Not
        (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
            (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
          (@Couret.STROBO2TORS.exceptionalSupports.{p2m_u_0} G inst inst_1 inst_2) S) →
      @Eq.{1} Nat
        (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.nontranslatedNeighbours.{p2m_u_0} G inst inst_1 inst_2 S))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := @_root_.Couret.STROBO2TORS.p2m_local_nontranslatedNeighbours_card_ordinary

