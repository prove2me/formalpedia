-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeGraph_edges_numeric
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:58:14.931218+00:00
-- url     : https://prove2.me/submissions/b05453c1-165f-4145-9278-f963673b5db6

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
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeGraph_mul_edges
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























/-- The universal quotient is exact, including its natural-number boundary cases. -/
theorem p2m_local_zeroFreeGraph_edges_numeric (Γ : SimpleGraph (Finset G))
    [DecidableRel Γ.Adj] (u : ℕ)
    (htrans : ∀ S T a, Γ.Adj (translateSupport S a) (translateSupport T a) ↔
      Γ.Adj S T)
    (hunion : ∀ S T, Γ.Adj S T → (S ∪ T).card = u) :
    (zeroFreeGraph Γ).edgeFinset.card =
      (Fintype.card G - u) * Γ.edgeFinset.card / Fintype.card G := by
  rw [← zeroFreeGraph_mul_edges Γ u htrans hunion]
  simp


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
        (@Finset.card.{p2m_u_0} (Sym2.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@SimpleGraph.edgeFinset.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.zeroFreeGraph.{p2m_u_0} G inst Γ)
            (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G)
              (@Couret.STROBO2TORS.zeroFreeGraph.{p2m_u_0} G inst Γ)
              (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2))
              (@Couret.STROBO2TORS.zeroFreeGraph_decidableRel.{p2m_u_0} G inst Γ))))
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Fintype.card.{p2m_u_0} G inst_2) u)
            (@Finset.card.{p2m_u_0} (Sym2.{p2m_u_0} (Finset.{p2m_u_0} G))
              (@SimpleGraph.edgeFinset.{p2m_u_0} (Finset.{p2m_u_0} G) Γ
                (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G) Γ
                  (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2)) inst_3))))
          (@Fintype.card.{p2m_u_0} G inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeGraph_edges_numeric

