-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeGraph_dart_filter_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:29:59.628983+00:00
-- url     : https://prove2.me/submissions/547c0a4b-805f-48a0-a8c8-b4dd15de3d38

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











theorem p2m_local_zeroFreeGraph_dart_filter_card (Γ : SimpleGraph (Finset G))
    [DecidableRel Γ.Adj] :
    ((Finset.univ : Finset Γ.Dart).filter
      (fun d => 0 ∉ d.fst ∪ d.snd)).card =
      Fintype.card (zeroFreeGraph Γ).Dart := by
  classical
  rw [← Finset.card_univ]
  let f : ∀ d ∈ ((Finset.univ : Finset Γ.Dart).filter
      (fun d => 0 ∉ d.fst ∪ d.snd)), (zeroFreeGraph Γ).Dart := by
    intro d hd
    have hzero : 0 ∉ d.fst ∧ 0 ∉ d.snd := by
      simpa only [Finset.mem_union, not_or] using (Finset.mem_filter.mp hd).2
    exact ⟨d.toProd, d.adj, hzero⟩
  apply Finset.card_bij f
  · intro d hd
    exact Finset.mem_univ _
  · intro d hd e he h
    exact SimpleGraph.Dart.ext _ _
      (congrArg (fun x : (zeroFreeGraph Γ).Dart => x.toProd) h)
  · intro d hd
    refine ⟨⟨d.toProd, d.adj.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union, not_or]
      exact d.adj.2
    · apply SimpleGraph.Dart.ext
      rfl














end Finite

end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (Γ : SimpleGraph.{p2m_u_0} (Finset.{p2m_u_0} G))
  [inst_3 :
    @DecidableRel.{p2m_u_0 + 1, p2m_u_0 + 1} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)
      (@SimpleGraph.Adj.{p2m_u_0} (Finset.{p2m_u_0} G) Γ)],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (@SimpleGraph.Dart.{p2m_u_0} (Finset.{p2m_u_0} G) Γ)
      (@Finset.filter.{p2m_u_0} (@SimpleGraph.Dart.{p2m_u_0} (Finset.{p2m_u_0} G) Γ)
        (fun d =>
          Not
            (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G))
              (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instUnion.{p2m_u_0} G inst_1)
                (@Prod.fst.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)
                  (@SimpleGraph.Dart.toProd.{p2m_u_0} (Finset.{p2m_u_0} G) Γ d))
                (@Prod.snd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)
                  (@SimpleGraph.Dart.toProd.{p2m_u_0} (Finset.{p2m_u_0} G) Γ d)))
              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_0} G
                  (@NegZeroClass.toZero.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))))
        (fun a =>
          @instDecidableNot
            (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G))
              (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instUnion.{p2m_u_0} G inst_1)
                (@Prod.fst.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)
                  (@SimpleGraph.Dart.toProd.{p2m_u_0} (Finset.{p2m_u_0} G) Γ a))
                (@Prod.snd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)
                  (@SimpleGraph.Dart.toProd.{p2m_u_0} (Finset.{p2m_u_0} G) Γ a)))
              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_0} G
                  (@NegZeroClass.toZero.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
            (@Finset.decidableMem.{p2m_u_0} G inst_1
              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_0} G
                  (@NegZeroClass.toZero.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
              (@Union.union.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instUnion.{p2m_u_0} G inst_1)
                (@Prod.fst.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)
                  (@SimpleGraph.Dart.toProd.{p2m_u_0} (Finset.{p2m_u_0} G) Γ a))
                (@Prod.snd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)
                  (@SimpleGraph.Dart.toProd.{p2m_u_0} (Finset.{p2m_u_0} G) Γ a)))))
        (@Finset.univ.{p2m_u_0} (@SimpleGraph.Dart.{p2m_u_0} (Finset.{p2m_u_0} G) Γ)
          (@SimpleGraph.Dart.fintype.{p2m_u_0} (Finset.{p2m_u_0} G) Γ (@Finset.fintype.{p2m_u_0} G inst_2) inst_3))))
    (@Fintype.card.{p2m_u_0}
      (@SimpleGraph.Dart.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.zeroFreeGraph.{p2m_u_0} G inst Γ))
      (@SimpleGraph.Dart.fintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.zeroFreeGraph.{p2m_u_0} G inst Γ)
        (@Finset.fintype.{p2m_u_0} G inst_2) (@Couret.STROBO2TORS.zeroFreeGraph_decidableRel.{p2m_u_0} G inst Γ))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeGraph_dart_filter_card

