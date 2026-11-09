-- Prove2me | solution 1 for Couret.STROBO2TORS.translation_incidence_card_balance
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:35.736996+00:00
-- url     : https://prove2.me/submissions/fd741fc4-0d6b-43ff-95da-89e5eab3a684

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
import Theorems.Thm_Couret_STROBO2TORS_translation_incidence_card
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



/-- The same double-counting identity without subtraction or a size hypothesis. -/
theorem p2m_local_translation_incidence_card_balance
    {X : Type*} [Fintype X] [DecidableEq X]
    (carrier : X → Finset G) (shift : G → X ≃ X)
    (hshift : ∀ a x, carrier (shift a x) = translateSupport (carrier x) a)
    (u : ℕ) (hcard : ∀ x, (carrier x).card = u) :
    Fintype.card G * ((Finset.univ : Finset X).filter
      (fun x => 0 ∉ carrier x)).card + u * Fintype.card X =
      Fintype.card G * Fintype.card X := by
  classical
  have h := translation_incidence_card carrier shift hshift u hcard
  rw [h]
  cases isEmpty_or_nonempty X with
  | inl hx =>
      letI := hx
      simp
  | inr hx =>
      obtain ⟨x⟩ := hx
      have hu : u ≤ Fintype.card G := by
        rw [← hcard x]
        exact Finset.card_le_univ _
      rw [← Nat.add_mul, Nat.sub_add_cancel hu]






















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
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
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
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) u (@Fintype.card.{p2m_u_1} X inst_3)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{p2m_u_0} G inst_2)
            (@Fintype.card.{p2m_u_1} X inst_3)) := @_root_.Couret.STROBO2TORS.p2m_local_translation_incidence_card_balance

