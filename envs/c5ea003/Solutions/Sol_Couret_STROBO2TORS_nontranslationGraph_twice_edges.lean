-- Prove2me | solution 1 for Couret.STROBO2TORS.nontranslationGraph_twice_edges
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:06.933199+00:00
-- url     : https://prove2.me/submissions/7f5092e1-2198-471a-b764-cba387fa8487

import Aesop
import Definitions.Def_Couret_Strobo2TorsNontranslationUnordered_7692bff20374
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_directed_nontranslation_degree_sum
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Theorems.Thm_Couret_STROBO2TORS_nontranslationGraph_degree
import Definitions.Def_Couret_Strobo2TorsNontranslationSymmetry_29c4a2e9c2a5
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]







/-- Exact double count: the sum of directed incidences is twice the
cardinality of the unordered edge set. -/
theorem p2m_local_nontranslationGraph_twice_edges :
    2 * (nontranslationGraph (G := G)).edgeFinset.card =
      (exceptionalSupports : Finset (Finset G)).card *
        (twoTorsion : Finset G).card := by
  classical
  have hHandshake :=
    (nontranslationGraph (G := G)).sum_degrees_eq_twice_card_edges
  have hFilter :
      (Finset.univ : Finset (Finset G)).filter (fun S => S.card = 3) =
        tripleSupports := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mem_tripleSupports S).symm
  have hSum :
      (∑ S : Finset G, (nontranslationGraph (G := G)).degree S) =
        ∑ S ∈ (tripleSupports : Finset (Finset G)),
          (nontranslatedNeighbours S).card := by
    calc
      (∑ S : Finset G, (nontranslationGraph (G := G)).degree S) =
          ∑ S : Finset G,
            (if S.card = 3 then (nontranslatedNeighbours S).card else 0) := by
              apply Finset.sum_congr rfl
              intro S _
              simpa only using nontranslationGraph_degree S
      _ = ∑ S ∈ ((Finset.univ : Finset (Finset G)).filter (fun S => S.card = 3)),
            (nontranslatedNeighbours S).card := by
              rw [Finset.sum_filter]
      _ = ∑ S ∈ (tripleSupports : Finset (Finset G)),
            (nontranslatedNeighbours S).card := by rw [hFilter]
  rw [hSum, directed_nontranslation_degree_sum] at hHandshake
  exact hHandshake.symm



end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@Finset.card.{p2m_u_0} (Sym2.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@SimpleGraph.edgeFinset.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.nontranslationGraph.{p2m_u_0} G inst inst_1 inst_2)
          (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.nontranslationGraph.{p2m_u_0} G inst inst_1 inst_2)
            (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2))
            (@Couret.STROBO2TORS.nontranslationGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2)))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.exceptionalSupports.{p2m_u_0} G inst inst_1 inst_2))
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_nontranslationGraph_twice_edges

