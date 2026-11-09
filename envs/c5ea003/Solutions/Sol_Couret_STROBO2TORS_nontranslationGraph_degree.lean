-- Prove2me | solution 1 for Couret.STROBO2TORS.nontranslationGraph_degree
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:40.455902+00:00
-- url     : https://prove2.me/submissions/b22584dd-0642-446b-9b18-d30eb9ef74a2

import Aesop
import Definitions.Def_Couret_Strobo2TorsNontranslationUnordered_7692bff20374
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsNontranslationSymmetry_29c4a2e9c2a5
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]





/-- Degree of a vertex equals the number of nontranslated square partners. -/
theorem p2m_local_nontranslationGraph_degree (S : Finset G) :
    (nontranslationGraph (G := G)).degree S =
      if hS : S.card = 3 then (nontranslatedNeighbours S).card else 0 := by
  classical
  have hNeighbors :
      (nontranslationGraph (G := G)).neighborFinset S =
        if S.card = 3 then nontranslatedNeighbours S else ∅ := by
    ext T
    by_cases hS : S.card = 3
    · simp [nontranslationGraph, hS]
    · simp [nontranslationGraph, hS]
  change ((nontranslationGraph (G := G)).neighborFinset S).card = _
  rw [hNeighbors]
  split_ifs <;> simp





end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  @Eq.{1} Nat
    (@SimpleGraph.degree.{p2m_u_0} (Finset.{p2m_u_0} G)
      (@Couret.STROBO2TORS.nontranslationGraph.{p2m_u_0} G inst inst_1 inst_2) S
      (@Subtype.fintype.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Set.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@Set.instMembership.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@SimpleGraph.neighborSet.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.nontranslationGraph.{p2m_u_0} G inst inst_1 inst_2) S))
        (fun a =>
          @SimpleGraph.neighborSet.memDecidable.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.nontranslationGraph.{p2m_u_0} G inst inst_1 inst_2) S
            (@Couret.STROBO2TORS.nontranslationGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2) a)
        (@Finset.fintype.{p2m_u_0} G inst_2)))
    (@dite.{1} Nat
      (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (instDecidableEqNat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (fun hS =>
        @Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.nontranslatedNeighbours.{p2m_u_0} G inst inst_1 inst_2 S))
      fun hS => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := @_root_.Couret.STROBO2TORS.p2m_local_nontranslationGraph_degree

