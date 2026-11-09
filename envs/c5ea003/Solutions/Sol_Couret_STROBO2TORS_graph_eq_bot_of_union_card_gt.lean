-- Prove2me | solution 1 for Couret.STROBO2TORS.graph_eq_bot_of_union_card_gt
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:52:09.291496+00:00
-- url     : https://prove2.me/submissions/fecc3dc7-48ee-445f-9e84-3fd51cbe1d3e

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeIncidence_e3b7fd015f51
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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
import Definitions.Def_Couret_Strobo2TorsDeltaCount_79a5ff554435
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Translation and incidence transfer from unrestricted collision pairs to pairs
whose two supports avoid zero. The incidence argument does not assume that
translation acts freely. This module adds to the historical certificates.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



















section Finite

variable [Fintype G]

















omit [AddCommGroup G] in
/-- If the prescribed union does not fit in the group, the entire family is empty. -/
theorem p2m_local_graph_eq_bot_of_union_card_gt (Γ : SimpleGraph (Finset G)) (u : ℕ)
    (hunion : ∀ S T, Γ.Adj S T → (S ∪ T).card = u)
    (hn : Fintype.card G < u) : Γ = ⊥ := by
  ext S T
  change Γ.Adj S T ↔ False
  constructor
  · intro h
    have hc := Finset.card_le_univ (S ∪ T)
    rw [hunion S T h] at hc
    omega
  · exact False.elim








end Finite

end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : DecidableEq.{p2m_u_0 + 1} G] [inst_1 : Fintype.{p2m_u_0} G]
  (Γ : SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G)) (u : Nat),
  (∀ (S T : Finset.{p2m_u_0} G),
      @SimpleGraph.Adj.{p2m_u_0} (Finset.{p2m_u_0} G) Γ S T →
        @Eq.{1} Nat
          (@Finset.card.{p2m_u_0} G
            (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instUnion.{p2m_u_0} G inst) S T))
          u) →
    @LT.lt.{0} Nat instLTNat (@Fintype.card.{p2m_u_0} G inst_1) u →
      @Eq.{p2m_u_0 + 1} (SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G)) Γ
        (@Bot.bot.{p2m_u_0} (SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@BooleanAlgebra.toBot.{p2m_u_0} (SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@CompleteBooleanAlgebra.toBooleanAlgebra.{p2m_u_0} (SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{p2m_u_0}
                (SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
                (@SimpleGraph.completeAtomicBooleanAlgebra.{p2m_u_0} (Finset.{p2m_u_0} G)))))) := @_root_.Couret.STROBO2TORS.p2m_local_graph_eq_bot_of_union_card_gt

