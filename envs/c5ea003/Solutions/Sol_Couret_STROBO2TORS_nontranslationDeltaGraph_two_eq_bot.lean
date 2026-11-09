-- Prove2me | solution 1 for Couret.STROBO2TORS.nontranslationDeltaGraph_two_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:49.625429+00:00
-- url     : https://prove2.me/submissions/fd68884a-c1a5-456c-8540-8dc26dcc1920

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
import Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_adj_iff
import Theorems.Thm_Couret_STROBO2TORS_orderedSquare_symmDiff_two_iff
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











/-- Delta two has no nontranslation edge. -/
theorem p2m_local_nontranslationDeltaGraph_two_eq_bot :
    nontranslationDeltaGraph (G := G) 2 = ⊥ := by
  ext S T
  change (nontranslationDeltaGraph (G := G) 2).Adj S T ↔ False
  constructor
  · intro h
    rcases (nontranslationDeltaGraph_adj_iff S T 2).mp h with
      ⟨hS, hT, hsq, hnot, hdelta⟩
    obtain ⟨u, _, hTu⟩ :=
      ((orderedSquare_symmDiff_two_iff S T hS hT).mp ⟨hsq, hdelta⟩).1
    exact hnot ⟨u, hTu⟩
  · exact False.elim






















end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
    (@Couret.STROBO2TORS.nontranslationDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@Bot.bot.{p2m_u_0} (SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@BooleanAlgebra.toBot.{p2m_u_0} (SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@CompleteBooleanAlgebra.toBooleanAlgebra.{p2m_u_0} (SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{p2m_u_0} (SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@SimpleGraph.completeAtomicBooleanAlgebra.{p2m_u_0} (Finset.{p2m_u_0} G)))))) := @_root_.Couret.STROBO2TORS.p2m_local_nontranslationDeltaGraph_two_eq_bot

