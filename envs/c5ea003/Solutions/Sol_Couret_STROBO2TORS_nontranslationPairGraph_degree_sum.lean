-- Prove2me | solution 1 for Couret.STROBO2TORS.nontranslationPairGraph_degree_sum
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:10.31242+00:00
-- url     : https://prove2.me/submissions/745138b3-53cd-47a9-af76-563ad365bd23

import Aesop
import Definitions.Def_Couret_Strobo2TorsUnorderedPairs_09c78b93fb82
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Definitions.Def_Couret_Strobo2TorsNontranslationDegree_16ff2822736a
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]







theorem nontranslationPairGraph_neighborFinset_eq (S : Finset G)
    (hS : S.card = 3) :
    (nontranslationPairGraph (G := G)).neighborFinset S =
      nontranslatedNeighbours S := by
  classical
  ext T
  simp [SimpleGraph.mem_neighborFinset, nontranslationPairGraph, hS]

theorem nontranslationPairGraph_neighborFinset_empty (S : Finset G)
    (hS : S.card ≠ 3) :
    (nontranslationPairGraph (G := G)).neighborFinset S = ∅ := by
  classical
  ext T
  simp [SimpleGraph.mem_neighborFinset, nontranslationPairGraph, hS]

theorem nontranslationPairGraph_degree_of_triple (S : Finset G)
    (hS : S.card = 3) :
    (nontranslationPairGraph (G := G)).degree S =
      (nontranslatedNeighbours S).card := by
  classical
  change ((nontranslationPairGraph (G := G)).neighborFinset S).card = _
  rw [nontranslationPairGraph_neighborFinset_eq S hS]

theorem nontranslationPairGraph_degree_of_not_triple (S : Finset G)
    (hS : S.card ≠ 3) :
    (nontranslationPairGraph (G := G)).degree S = 0 := by
  classical
  change ((nontranslationPairGraph (G := G)).neighborFinset S).card = 0
  rw [nontranslationPairGraph_neighborFinset_empty S hS]
  simp

/-- The degree sum over every possible finite support equals the true
directed incidence count: all vertices outside tripleSupports are isolated. -/
theorem p2m_local_nontranslationPairGraph_degree_sum :
    (∑ S : Finset G, (nontranslationPairGraph (G := G)).degree S) =
      (∑ S ∈ (tripleSupports : Finset (Finset G)),
        (nontranslatedNeighbours S).card) := by
  classical
  calc
    (∑ S : Finset G, (nontranslationPairGraph (G := G)).degree S) =
      (∑ S : Finset G,
        if S.card = 3 then (nontranslatedNeighbours S).card else 0) := by
          apply Finset.sum_congr rfl
          intro S _
          split_ifs with hS
          · exact nontranslationPairGraph_degree_of_triple S hS
          · exact nontranslationPairGraph_degree_of_not_triple S hS
    _ = ∑ S ∈ ((Finset.univ : Finset (Finset G)).filter
          (fun S => S.card = 3)), (nontranslatedNeighbours S).card := by
          rw [Finset.sum_filter]
    _ = ∑ S ∈ (tripleSupports : Finset (Finset G)),
          (nontranslatedNeighbours S).card := by
          have hFilter : (Finset.univ : Finset (Finset G)).filter
              (fun S => S.card = 3) = tripleSupports := by
            ext S
            simp [mem_tripleSupports]
          rw [hFilter]







end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.sum.{p2m_u_0, 0} (Finset.{p2m_u_0} G) Nat Nat.instAddCommMonoid
      (@Finset.univ.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2)) fun S =>
      @SimpleGraph.degree.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.nontranslationPairGraph.{p2m_u_0} G inst inst_1 inst_2) S
        (@Couret.STROBO2TORS.nontranslationGraphNeighborFintype.{p2m_u_0} G inst inst_1 inst_2 S))
    (@Finset.sum.{p2m_u_0, 0} (Finset.{p2m_u_0} G) Nat Nat.instAddCommMonoid
      (@Couret.STROBO2TORS.tripleSupports.{p2m_u_0} G inst_2) fun S =>
      @Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.nontranslatedNeighbours.{p2m_u_0} G inst inst_1 inst_2 S)) := @_root_.Couret.STROBO2TORS.p2m_local_nontranslationPairGraph_degree_sum

