-- Prove2me | solution 1 for Couret.STROBO2TORS.translation_incidence_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:29:47.487337+00:00
-- url     : https://prove2.me/submissions/bfb0f028-4558-4f44-8e66-d6c094745f43

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





@[simp] theorem add_mem_translateSupport_iff (S : Finset G) (x a : G) :
    x + a ∈ translateSupport S a ↔ x ∈ S := by
  simp [translateSupport]













section Finite

variable [Fintype G]

/-- The incidence identity for a finite translation-invariant collection.
Only bijectivity of each shift is needed; stabilizers are unrestricted. -/
theorem p2m_local_translation_incidence_card
    {X : Type*} [Fintype X] [DecidableEq X]
    (carrier : X → Finset G) (shift : G → X ≃ X)
    (hshift : ∀ a x, carrier (shift a x) = translateSupport (carrier x) a)
    (u : ℕ) (hcard : ∀ x, (carrier x).card = u) :
    Fintype.card G * ((Finset.univ : Finset X).filter
      (fun x => 0 ∉ carrier x)).card =
      (Fintype.card G - u) * Fintype.card X := by
  classical
  have hpoint (a : G) :
      ((Finset.univ : Finset X).filter (fun x => a ∉ carrier x)).card =
        ((Finset.univ : Finset X).filter (fun x => 0 ∉ carrier x)).card := by
    apply Finset.card_bijective (shift a).symm (shift a).symm.bijective
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hx := hshift a ((shift a).symm x)
    rw [(shift a).apply_symm_apply] at hx
    rw [hx]
    simpa only [zero_add] using
      (not_congr (add_mem_translateSupport_iff (carrier ((shift a).symm x)) 0 a))
  have hrow (x : X) :
      ((Finset.univ : Finset G).filter (fun a => a ∉ carrier x)).card =
        Fintype.card G - u := by
    have heq : (Finset.univ : Finset G).filter (fun a => a ∈ carrier x) =
        carrier x := by ext a; simp
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset G)) (fun a => a ∈ carrier x)
    rw [heq, hcard x, Finset.card_univ] at h
    omega
  calc
    _ = ∑ a : G, ((Finset.univ : Finset X).filter
        (fun x => a ∉ carrier x)).card := by simp [hpoint]
    _ = ∑ x : X, ((Finset.univ : Finset G).filter
        (fun a => a ∉ carrier x)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    _ = _ := by simp [hrow, Nat.mul_comm]
























end Finite

end Couret.STROBO2TORS

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] {X : Type p2m_u_1} [inst_3 : Fintype.{p2m_u_1} X] [DecidableEq.{p2m_u_1 + 1} X]
  (carrier : X → Finset.{p2m_u_0} G) (shift : G → Equiv.{p2m_u_1 + 1, p2m_u_1 + 1} X X),
  (∀ (a : G) (x : X),
      @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
        (carrier
          (@DFunLike.coe.{p2m_u_1 + 1, p2m_u_1 + 1, p2m_u_1 + 1} (Equiv.{p2m_u_1 + 1, p2m_u_1 + 1} X X) X (fun x => X)
            (@EquivLike.toFunLike.{p2m_u_1 + 1, p2m_u_1 + 1, p2m_u_1 + 1} (Equiv.{p2m_u_1 + 1, p2m_u_1 + 1} X X) X X
              (@Equiv.instEquivLike.{p2m_u_1 + 1, p2m_u_1 + 1} X X))
            (shift a) x))
        (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 (carrier x) a)) →
    ∀ (u : Nat),
      (∀ (x : X), @Eq.{1} Nat (@Finset.card.{p2m_u_0} G (carrier x)) u) →
        @Eq.{1} Nat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{p2m_u_0} G inst_2)
            (@Finset.card.{p2m_u_1} X
              (@Finset.filter.{p2m_u_1} X
                (fun x =>
                  Not
                    (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G
                        (@Finset.instSetLike.{p2m_u_0} G))
                      (carrier x)
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
                      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G
                        (@Finset.instSetLike.{p2m_u_0} G))
                      (carrier a)
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
                      (carrier a)))
                (@Finset.univ.{p2m_u_1} X inst_3))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Fintype.card.{p2m_u_0} G inst_2) u)
            (@Fintype.card.{p2m_u_1} X inst_3)) := @_root_.Couret.STROBO2TORS.p2m_local_translation_incidence_card

