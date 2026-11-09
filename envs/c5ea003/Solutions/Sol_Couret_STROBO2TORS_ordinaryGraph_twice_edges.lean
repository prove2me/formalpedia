-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryGraph_twice_edges
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:16:47.935898+00:00
-- url     : https://prove2.me/submissions/a8d70a0b-7dee-4704-b49b-0e9081a352d8

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
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Theorems.Thm_Couret_STROBO2TORS_ordinaryGraph_neighborFinset
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_tripleSupports_card
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







/-- Every triple has h - 1 ordinary neighbours; all other vertices are isolated. -/
theorem ordinaryGraph_degree (S : Finset G) :
    (ordinaryGraph (G := G)).degree S =
      if S.card = 3 then (twoTorsion : Finset G).card - 1 else 0 := by
  classical
  have hSelf : S ∈ torsionOrbit S := by
    apply (mem_torsionOrbit S S).mpr
    exact ⟨0, by simp, by simp [translateSupport]⟩
  change ((ordinaryGraph (G := G)).neighborFinset S).card = _
  rw [ordinaryGraph_neighborFinset]
  by_cases hS : S.card = 3
  · simp only [if_pos hS]
    rw [Finset.card_erase_of_mem hSelf, torsionOrbit_card S hS]
  · simp [hS]

/-- The handshake count includes every triple, including those containing zero. -/
theorem p2m_local_ordinaryGraph_twice_edges :
    2 * (ordinaryGraph (G := G)).edgeFinset.card =
      (Fintype.card G).choose 3 * ((twoTorsion : Finset G).card - 1) := by
  classical
  have hHandshake := (ordinaryGraph (G := G)).sum_degrees_eq_twice_card_edges
  have hFilter :
      (Finset.univ : Finset (Finset G)).filter (fun S => S.card = 3) =
        tripleSupports := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mem_tripleSupports S).symm
  have hSum :
      (∑ S : Finset G, (ordinaryGraph (G := G)).degree S) =
        (Fintype.card G).choose 3 * ((twoTorsion : Finset G).card - 1) := by
    calc
      (∑ S : Finset G, (ordinaryGraph (G := G)).degree S) =
          ∑ S : Finset G,
            (if S.card = 3 then (twoTorsion : Finset G).card - 1 else 0) := by
              apply Finset.sum_congr rfl
              intro S _
              exact ordinaryGraph_degree S
      _ = ∑ _S ∈ ((Finset.univ : Finset (Finset G)).filter (fun S => S.card = 3)),
            ((twoTorsion : Finset G).card - 1) := by
              rw [Finset.sum_filter]
      _ = _ := by
        rw [hFilter]
        simp [tripleSupports_card]
  rw [hSum] at hHandshake
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
          (@Couret.STROBO2TORS.ordinaryGraph.{p2m_u_0} G inst inst_1)
          (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.ordinaryGraph.{p2m_u_0} G inst inst_1)
            (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2))
            (@Couret.STROBO2TORS.ordinaryGraph_decidableRel.{p2m_u_0} G inst inst_1)))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (Nat.choose (@Fintype.card.{p2m_u_0} G inst_2) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryGraph_twice_edges

