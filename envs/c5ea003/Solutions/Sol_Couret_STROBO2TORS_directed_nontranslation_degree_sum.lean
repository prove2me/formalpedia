-- Prove2me | solution 1 for Couret.STROBO2TORS.directed_nontranslation_degree_sum
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:50.004485+00:00
-- url     : https://prove2.me/submissions/db9bcf60-f494-4d4f-a2d3-8a9980b4130c

import Aesop
import Definitions.Def_Couret_Strobo2TorsNontranslationDegree_16ff2822736a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Theorems.Thm_Couret_STROBO2TORS_nontranslatedNeighbours_card_exceptional
import Theorems.Thm_Couret_STROBO2TORS_nontranslatedNeighbours_card_ordinary
import Definitions.Def_Couret_Strobo2TorsNontranslationBridge_e18319b1ae30
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]











/-- All source triples contribute h or zero according to the existing
exceptional-support classification. -/
theorem nontranslatedNeighbours_card_ite (S : Finset G)
    (hS : S.card = 3) :
    (nontranslatedNeighbours S).card =
      if S ∈ (exceptionalSupports : Finset (Finset G))
      then (twoTorsion : Finset G).card else 0 := by
  by_cases hExc : S ∈ (exceptionalSupports : Finset (Finset G))
  · rw [if_pos hExc]
    exact nontranslatedNeighbours_card_exceptional S hExc
  · rw [if_neg hExc]
    exact nontranslatedNeighbours_card_ordinary S hS hExc

/-- Total number of directed incidences (source triple, nontranslated
partner) is the number of exceptional supports times h. -/
theorem p2m_local_directed_nontranslation_degree_sum :
    (∑ S ∈ (tripleSupports : Finset (Finset G)),
        (nontranslatedNeighbours S).card) =
      (exceptionalSupports : Finset (Finset G)).card *
        (twoTorsion : Finset G).card := by
  have hSubset :
      (exceptionalSupports : Finset (Finset G)) ⊆ tripleSupports := by
    intro S hExc
    exact (mem_tripleSupports S).mpr
      ((mem_exceptionalSupports_card S).mp hExc).1
  have hFilter :
      (tripleSupports : Finset (Finset G)).filter
        (fun S => S ∈ (exceptionalSupports : Finset (Finset G))) =
          exceptionalSupports := by
    ext S
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).2
    · intro h
      exact Finset.mem_filter.mpr ⟨hSubset h, h⟩
  calc
    (∑ S ∈ (tripleSupports : Finset (Finset G)),
        (nontranslatedNeighbours S).card) =
      ∑ S ∈ (tripleSupports : Finset (Finset G)),
        (if S ∈ (exceptionalSupports : Finset (Finset G))
          then (twoTorsion : Finset G).card else 0) := by
            apply Finset.sum_congr rfl
            intro S hS
            exact nontranslatedNeighbours_card_ite S
              ((mem_tripleSupports S).mp hS)
    _ = ∑ S ∈ ((tripleSupports : Finset (Finset G)).filter
          (fun S => S ∈ (exceptionalSupports : Finset (Finset G)))),
          (twoTorsion : Finset G).card := by
            rw [Finset.sum_filter]
    _ = (exceptionalSupports : Finset (Finset G)).card *
          (twoTorsion : Finset G).card := by
            rw [hFilter]
            simp



end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.sum.{p2m_u_0, 0} (Finset.{p2m_u_0} G) Nat Nat.instAddCommMonoid
      (@Couret.STROBO2TORS.tripleSupports.{p2m_u_0} G inst_2) fun S =>
      @Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.nontranslatedNeighbours.{p2m_u_0} G inst inst_1 inst_2 S))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.exceptionalSupports.{p2m_u_0} G inst inst_1 inst_2))
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_directed_nontranslation_degree_sum

