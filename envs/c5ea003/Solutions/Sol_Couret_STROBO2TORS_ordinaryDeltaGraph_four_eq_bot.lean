-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryDeltaGraph_four_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:54.899204+00:00
-- url     : https://prove2.me/submissions/a790d8cc-746b-4c78-9cac-6f36b57a534d

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

















/-- An ordinary edge has delta two or six, never four. -/
theorem ordinaryGraph_adj_delta_cases (S T : Finset G)
    (h : (ordinaryGraph (G := G)).Adj S T) :
    (S ∆ T).card = 2 ∨ (S ∆ T).card = 6 := by
  rcases ordinaryPartner_inter_card_eq_zero_or_two S T h.1 h.2.1 h.2.2.1 h.2.2.2
      with hZero | hTwo
  · exact Or.inr ((triple_symmDiff_six_iff_inter_zero S T h.1 h.2.1).mpr hZero)
  · exact Or.inl ((triple_symmDiff_two_iff_inter_two S T h.1 h.2.1).mpr hTwo)

/-- The delta four stratum contains no ordinary edge. -/
theorem p2m_local_ordinaryDeltaGraph_four_eq_bot :
    ordinaryDeltaGraph (G := G) 4 = ⊥ := by
  ext S T
  change ((ordinaryGraph (G := G)).Adj S T ∧ (S ∆ T).card = 4) ↔ False
  constructor
  · intro h
    have hCases := ordinaryGraph_adj_delta_cases S T h.1
    omega
  · exact False.elim








end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
    (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
    (@Bot.bot.{p2m_u_0} (SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@BooleanAlgebra.toBot.{p2m_u_0} (SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@CompleteBooleanAlgebra.toBooleanAlgebra.{p2m_u_0} (SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{p2m_u_0} (SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@SimpleGraph.completeAtomicBooleanAlgebra.{p2m_u_0} (Finset.{p2m_u_0} G)))))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryDeltaGraph_four_eq_bot

