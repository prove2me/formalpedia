-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryGraph_neighborFinset
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:39.912516+00:00
-- url     : https://prove2.me/submissions/10a6f1ec-61a1-42a3-9885-eaf710703f48

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





/-- The ordinary neighbours are the two-torsion orbit with the source removed. -/
theorem p2m_local_ordinaryGraph_neighborFinset (S : Finset G) :
    (ordinaryGraph (G := G)).neighborFinset S =
      if S.card = 3 then (torsionOrbit S).erase S else ∅ := by
  classical
  ext T
  by_cases hS : S.card = 3
  · rw [if_pos hS, SimpleGraph.mem_neighborFinset]
    change (S.card = 3 ∧ T.card = 3 ∧ S ≠ T ∧ OrdinaryPartner S T) ↔ _
    rw [Finset.mem_erase, mem_torsionOrbit]
    constructor
    · rintro ⟨_, _, hST, ho⟩
      exact ⟨hST.symm, ho⟩
    · rintro ⟨hTS, ho⟩
      refine ⟨hS, ?_, hTS.symm, ho⟩
      obtain ⟨u, _, hTu⟩ := ho
      rw [hTu, translateSupport_card]
      exact hS
  · simp [ordinaryGraph, hS]






















end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
    (@SimpleGraph.neighborFinset.{p2m_u_0} (Finset.{p2m_u_0} G)
      (@Couret.STROBO2TORS.ordinaryGraph.{p2m_u_0} G inst inst_1) S
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
    (@ite.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (instDecidableEqNat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@Finset.erase.{p2m_u_0} (Finset.{p2m_u_0} G) (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
        (@Couret.STROBO2TORS.torsionOrbit.{p2m_u_0} G inst inst_1 inst_2 S) S)
      (@EmptyCollection.emptyCollection.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Finset.instEmptyCollection.{p2m_u_0} (Finset.{p2m_u_0} G)))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryGraph_neighborFinset

