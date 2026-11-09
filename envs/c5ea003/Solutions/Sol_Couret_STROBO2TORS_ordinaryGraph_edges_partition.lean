-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryGraph_edges_partition
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:16:52.782071+00:00
-- url     : https://prove2.me/submissions/ac2218c8-d528-4f71-ab85-9c8bd704b879

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
import Theorems.Thm_Couret_STROBO2TORS_ordinaryGraph_degree_partition
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























/-- Every unordered ordinary edge lies in exactly one of the delta two and six classes. -/
theorem p2m_local_ordinaryGraph_edges_partition :
    (ordinaryGraph (G := G)).edgeFinset.card =
      (ordinaryDeltaGraph (G := G) 2).edgeFinset.card +
        (ordinaryDeltaGraph (G := G) 6).edgeFinset.card := by
  classical
  have hSum :
      (∑ S : Finset G, (ordinaryGraph (G := G)).degree S) =
        (∑ S : Finset G, (ordinaryDeltaGraph (G := G) 2).degree S) +
          (∑ S : Finset G, (ordinaryDeltaGraph (G := G) 6).degree S) := by
    calc
      (∑ S : Finset G, (ordinaryGraph (G := G)).degree S) =
          ∑ S : Finset G, ((ordinaryDeltaGraph (G := G) 2).degree S +
            (ordinaryDeltaGraph (G := G) 6).degree S) := by
              apply Finset.sum_congr rfl
              intro S _
              exact ordinaryGraph_degree_partition S
      _ = _ := Finset.sum_add_distrib
  rw [(ordinaryGraph (G := G)).sum_degrees_eq_twice_card_edges,
    (ordinaryDeltaGraph (G := G) 2).sum_degrees_eq_twice_card_edges,
    (ordinaryDeltaGraph (G := G) 6).sum_degrees_eq_twice_card_edges] at hSum
  omega




end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Sym2.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@SimpleGraph.edgeFinset.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.ordinaryGraph.{p2m_u_0} G inst inst_1)
        (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.ordinaryGraph.{p2m_u_0} G inst inst_1)
          (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2))
          (@Couret.STROBO2TORS.ordinaryGraph_decidableRel.{p2m_u_0} G inst inst_1))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@Finset.card.{p2m_u_0} (Sym2.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@SimpleGraph.edgeFinset.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2))
            (@Couret.STROBO2TORS.ordinaryDeltaGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (@Finset.card.{p2m_u_0} (Sym2.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@SimpleGraph.edgeFinset.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2))
            (@Couret.STROBO2TORS.ordinaryDeltaGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryGraph_edges_partition

