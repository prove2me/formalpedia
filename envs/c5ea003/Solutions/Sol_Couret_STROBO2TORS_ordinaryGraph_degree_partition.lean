-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryGraph_degree_partition
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:43.740891+00:00
-- url     : https://prove2.me/submissions/291ffd66-266c-4d66-a296-5e33e742ea25

import Aesop
import Definitions.Def_Couret_Strobo2TorsDeltaOrdinaryCount_91279c99d3e0
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryPartner_inter_card_eq_zero_or_two
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_six_iff_inter_zero
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_two_iff_inter_two
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Ordinary collision edges on all triple supports, with zero permitted.
The action of the two-torsion subgroup is free on a three-element support.
Consequently every triple has exactly h - 1 distinct ordinary neighbours.
The certified intersection subdivision partitions these edges into delta
two and delta six; this module does not identify ordinary fibres with all
ordinary partner edges, since exceptional fibres contain such edges too.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]















/-- The delta restriction filters the ordinary neighbour set. -/
theorem ordinaryDeltaGraph_degree (S : Finset G) (k : ℕ) :
    (ordinaryDeltaGraph (G := G) k).degree S =
      (((ordinaryGraph (G := G)).neighborFinset S).filter
        (fun T => (S ∆ T).card = k)).card := by
  classical
  have hNeighbours :
      (ordinaryDeltaGraph (G := G) k).neighborFinset S =
        ((ordinaryGraph (G := G)).neighborFinset S).filter
          (fun T => (S ∆ T).card = k) := by
    ext T
    simp [ordinaryDeltaGraph]
  change ((ordinaryDeltaGraph (G := G) k).neighborFinset S).card = _
  rw [hNeighbours]

/-- An ordinary edge has delta two or six, never four. -/
theorem ordinaryGraph_adj_delta_cases (S T : Finset G)
    (h : (ordinaryGraph (G := G)).Adj S T) :
    (S ∆ T).card = 2 ∨ (S ∆ T).card = 6 := by
  rcases ordinaryPartner_inter_card_eq_zero_or_two S T h.1 h.2.1 h.2.2.1 h.2.2.2
      with hZero | hTwo
  · exact Or.inr ((triple_symmDiff_six_iff_inter_zero S T h.1 h.2.1).mpr hZero)
  · exact Or.inl ((triple_symmDiff_two_iff_inter_two S T h.1 h.2.1).mpr hTwo)



/-- The two possible delta classes partition the ordinary degree at each vertex. -/
theorem p2m_local_ordinaryGraph_degree_partition (S : Finset G) :
    (ordinaryGraph (G := G)).degree S =
      (ordinaryDeltaGraph (G := G) 2).degree S +
        (ordinaryDeltaGraph (G := G) 6).degree S := by
  classical
  have hFilter :
      ((ordinaryGraph (G := G)).neighborFinset S).filter
          (fun T => (S ∆ T).card ≠ 2) =
        ((ordinaryGraph (G := G)).neighborFinset S).filter
          (fun T => (S ∆ T).card = 6) := by
    ext T
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hT, hNot⟩
      have hAdj : (ordinaryGraph (G := G)).Adj S T := by simpa using hT
      exact ⟨hT, (ordinaryGraph_adj_delta_cases S T hAdj).resolve_left hNot⟩
    · rintro ⟨hT, hSix⟩
      exact ⟨hT, by omega⟩
  have hCard := Finset.card_filter_add_card_filter_not
    (s := (ordinaryGraph (G := G)).neighborFinset S)
    (fun T => (S ∆ T).card = 2)
  rw [hFilter] at hCard
  rw [ordinaryDeltaGraph_degree S 2, ordinaryDeltaGraph_degree S 6]
  change ((ordinaryGraph (G := G)).neighborFinset S).card = _
  exact hCard.symm






end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  @Eq.{1} Nat
    (@SimpleGraph.degree.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.ordinaryGraph.{p2m_u_0} G inst inst_1) S
      (@Subtype.fintype.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Set.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@Set.instMembership.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@SimpleGraph.neighborSet.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.ordinaryGraph.{p2m_u_0} G inst inst_1) S))
        (fun a =>
          @SimpleGraph.neighborSet.memDecidable.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.ordinaryGraph.{p2m_u_0} G inst inst_1) S
            (@Couret.STROBO2TORS.ordinaryGraph_decidableRel.{p2m_u_0} G inst inst_1) a)
        (@Finset.fintype.{p2m_u_0} G inst_2)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@SimpleGraph.degree.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        S
        (@Subtype.fintype.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Set.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Set.instMembership.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@SimpleGraph.neighborSet.{p2m_u_0} (Finset.{p2m_u_0} G)
              (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              S))
          (fun a =>
            @SimpleGraph.neighborSet.memDecidable.{p2m_u_0} (Finset.{p2m_u_0} G)
              (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              S
              (@Couret.STROBO2TORS.ordinaryDeltaGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              a)
          (@Finset.fintype.{p2m_u_0} G inst_2)))
      (@SimpleGraph.degree.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
        S
        (@Subtype.fintype.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Set.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Set.instMembership.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@SimpleGraph.neighborSet.{p2m_u_0} (Finset.{p2m_u_0} G)
              (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              S))
          (fun a =>
            @SimpleGraph.neighborSet.memDecidable.{p2m_u_0} (Finset.{p2m_u_0} G)
              (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              S
              (@Couret.STROBO2TORS.ordinaryDeltaGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              a)
          (@Finset.fintype.{p2m_u_0} G inst_2)))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryGraph_degree_partition

