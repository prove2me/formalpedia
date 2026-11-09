-- Prove2me | solution 1 for Couret.STROBO2TORS.squareDeltaGraph_four_twice_edges_numeric
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:42:44.95838+00:00
-- url     : https://prove2.me/submissions/cecdd7a0-0fc3-4317-8add-3774b331a9bd

import Aesop
import Definitions.Def_Couret_Strobo2TorsDeltaCount_79a5ff554435
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_four_twice_edges_numeric
import Theorems.Thm_Couret_STROBO2TORS_ordinaryDeltaGraph_four_eq_bot
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_edges_partition
import Definitions.Def_Couret_Strobo2TorsDeltaTwoCount_96c8f007ba6a
import Definitions.Def_Couret_Strobo2TorsDeltaExceptionalCount_9f9783d90924
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Exact unordered pair counts at symmetric-difference sizes two, four and six.
The vertices are three-element subsets of a finite abelian group; zero is
permitted. The graph adjacency theorem identifies the counted objects with
the labelled ordered convolution square, including diagonal pairs.
The two branch graphs have disjoint neighbour sets, so their edge counts
add. Natural-number subtraction is used throughout, including small groups.
-/

namespace Couret.STROBO2TORS





variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



















/-- Twice the total unordered delta-four count. -/
theorem p2m_local_squareDeltaGraph_four_twice_edges_numeric :
    2 * (squareDeltaGraph (G := G) 4).edgeFinset.card =
      Fintype.card G * ((twoTorsion : Finset G).card - 1) *
        ((threeTorsion : Finset G).card - 1) := by
  have hEmpty : (ordinaryDeltaGraph (G := G) 4).edgeFinset = ∅ :=
    SimpleGraph.edgeFinset_eq_empty.mpr ordinaryDeltaGraph_four_eq_bot
  rw [squareDeltaGraph_edges_partition, hEmpty, Finset.card_empty, Nat.zero_add]
  exact nontranslationDeltaGraph_four_twice_edges_numeric (G := G)














end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@Finset.card.{p2m_u_0} (Sym2.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@SimpleGraph.edgeFinset.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.squareDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.squareDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2))
            (@Couret.STROBO2TORS.squareDeltaGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{p2m_u_0} G inst_2)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_squareDeltaGraph_four_twice_edges_numeric

