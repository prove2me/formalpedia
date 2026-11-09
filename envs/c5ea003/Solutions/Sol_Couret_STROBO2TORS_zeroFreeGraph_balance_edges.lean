-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeGraph_balance_edges
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:58:11.967073+00:00
-- url     : https://prove2.me/submissions/4eb5e880-8d29-4ea6-866e-29ecbbb2ce18

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
import Theorems.Thm_Couret_STROBO2TORS_translation_incidence_card_balance
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeGraph_dart_filter_card
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







theorem translateSupport_union (S T : Finset G) (a : G) :
    translateSupport (S ∪ T) a = translateSupport S a ∪ translateSupport T a := by
  exact Finset.image_union _ _











section Finite

variable [Fintype G]















/-- The balanced incidence equation is valid for every finite abelian group. -/
theorem p2m_local_zeroFreeGraph_balance_edges (Γ : SimpleGraph (Finset G))
    [DecidableRel Γ.Adj] (u : ℕ)
    (htrans : ∀ S T a, Γ.Adj (translateSupport S a) (translateSupport T a) ↔
      Γ.Adj S T)
    (hunion : ∀ S T, Γ.Adj S T → (S ∪ T).card = u) :
    Fintype.card G * (zeroFreeGraph Γ).edgeFinset.card + u * Γ.edgeFinset.card =
      Fintype.card G * Γ.edgeFinset.card := by
  classical
  have h := translation_incidence_card_balance
    (fun d : Γ.Dart => d.fst ∪ d.snd) (dartTranslateEquiv Γ htrans)
    (by intro a d; exact (translateSupport_union d.fst d.snd a).symm)
    u (fun d => hunion d.fst d.snd d.adj)
  rw [zeroFreeGraph_dart_filter_card, (zeroFreeGraph Γ).dart_card_eq_twice_card_edges,
    Γ.dart_card_eq_twice_card_edges] at h
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
  calc
    2 * (Fintype.card G * (zeroFreeGraph Γ).edgeFinset.card +
        u * Γ.edgeFinset.card) =
      Fintype.card G * (2 * (zeroFreeGraph Γ).edgeFinset.card) +
        u * (2 * Γ.edgeFinset.card) := by ring
    _ = Fintype.card G * (2 * Γ.edgeFinset.card) := h
    _ = 2 * (Fintype.card G * Γ.edgeFinset.card) := by ring










end Finite

end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (Γ : SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
  [inst_3 :
    @DecidableRel.{p2m_u_0 + 1, p2m_u_0 + 1} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)
      (@SimpleGraph.Adj.{p2m_u_0} (Finset.{p2m_u_0} G) Γ)]
  (u : Nat),
  (∀ (S T : Finset.{p2m_u_0} G) (a : G),
      Iff
        (@SimpleGraph.Adj.{p2m_u_0} (Finset.{p2m_u_0} G) Γ
          (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S a)
          (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 T a))
        (@SimpleGraph.Adj.{p2m_u_0} (Finset.{p2m_u_0} G) Γ S T)) →
    (∀ (S T : Finset.{p2m_u_0} G),
        @SimpleGraph.Adj.{p2m_u_0} (Finset.{p2m_u_0} G) Γ S T →
          @Eq.{1} Nat
            (@Finset.card.{p2m_u_0} G
              (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instUnion.{p2m_u_0} G inst_1) S T))
            u) →
      @Eq.{1} Nat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{p2m_u_0} G inst_2)
            (@Finset.card.{p2m_u_0} (Sym2.{p2m_u_0} (Finset.{p2m_u_0} G))
              (@SimpleGraph.edgeFinset.{p2m_u_0} (Finset.{p2m_u_0} G)
                (@Couret.STROBO2TORS.zeroFreeGraph.{p2m_u_0} G inst Γ)
                (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G)
                  (@Couret.STROBO2TORS.zeroFreeGraph.{p2m_u_0} G inst Γ)
                  (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2))
                  (@Couret.STROBO2TORS.zeroFreeGraph_decidableRel.{p2m_u_0} G inst Γ)))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) u
            (@Finset.card.{p2m_u_0} (Sym2.{p2m_u_0} (Finset.{p2m_u_0} G))
              (@SimpleGraph.edgeFinset.{p2m_u_0} (Finset.{p2m_u_0} G) Γ
                (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G) Γ
                  (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2)) inst_3)))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{p2m_u_0} G inst_2)
          (@Finset.card.{p2m_u_0} (Sym2.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@SimpleGraph.edgeFinset.{p2m_u_0} (Finset.{p2m_u_0} G) Γ
              (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G) Γ
                (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2)) inst_3)))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeGraph_balance_edges

