-- Prove2me | solution 1 for Couret.STROBO2TORS.deltaTwoOrderedPairs_iff_adj
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:13.233123+00:00
-- url     : https://prove2.me/submissions/e5b2d78e-3ebf-4a05-a437-866a0cd8359f

import Aesop
import Definitions.Def_Couret_Strobo2TorsDeltaTwoCount_96c8f007ba6a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_two_iff_inter_two
import Definitions.Def_Couret_Strobo2TorsDeltaOrdinaryCount_91279c99d3e0

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Exact count of the ordinary delta-two edges, with zero allowed.

Parameters (a,u,b) have u a nonzero element of G[2] and b outside
{a,a+u}. They represent the ordered pair
({a,a+u,b}, {a,a+u,b+u}). Each ordered pair has precisely two
parameters, according to the choice a or a+u in its common pair.
The graph handshake supplies the second factor of two.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]













variable [Fintype G]











attribute [local instance] Classical.propDecidable



theorem mem_deltaTwoOrderedPairs (S T : Finset G) :
    (S,T) ∈ deltaTwoOrderedPairs ↔
      S.card = 3 ∧ T.card = 3 ∧ OrdinaryPartner S T ∧ (S ∩ T).card = 2 := by
  simp only [deltaTwoOrderedPairs, Finset.mem_filter, Finset.mem_product,
    mem_tripleSupports]
  tauto











theorem p2m_local_deltaTwoOrderedPairs_iff_adj (S T : Finset G) :
    (S,T) ∈ deltaTwoOrderedPairs ↔ (ordinaryDeltaGraph (G := G) 2).Adj S T := by
  rw [mem_deltaTwoOrderedPairs]
  change (S.card = 3 ∧ T.card = 3 ∧ OrdinaryPartner S T ∧ (S ∩ T).card = 2) ↔
    (S.card = 3 ∧ T.card = 3 ∧ S ≠ T ∧ OrdinaryPartner S T) ∧ (S ∆ T).card = 2
  constructor
  · rintro ⟨hS,hT,hOrd,hI⟩
    have hne : S ≠ T := by
      intro heq
      rw [heq, Finset.inter_self, hT] at hI
      omega
    exact ⟨⟨hS,hT,hne,hOrd⟩,(triple_symmDiff_two_iff_inter_two S T hS hT).mpr hI⟩
  · rintro ⟨⟨hS,hT,_,hOrd⟩,hD⟩
    exact ⟨hS,hT,hOrd,(triple_symmDiff_two_iff_inter_two S T hS hT).mp hD⟩






end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S T : Finset.{p2m_u_0} G),
  Iff
    (@Membership.mem.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
      (Finset.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
        (Finset.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)))
        (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
        (@Finset.instSetLike.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))))
      (@Couret.STROBO2TORS.deltaTwoOrderedPairs.{p2m_u_0} G inst inst_1 inst_2)
      (@Prod.mk.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) S T))
    (@SimpleGraph.Adj.{p2m_u_0} (Finset.{p2m_u_0} G)
      (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      S T) := @_root_.Couret.STROBO2TORS.p2m_local_deltaTwoOrderedPairs_iff_adj

