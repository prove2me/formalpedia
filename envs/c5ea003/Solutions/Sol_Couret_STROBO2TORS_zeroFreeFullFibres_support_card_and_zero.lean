-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_support_card_and_zero
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:36.223323+00:00
-- url     : https://prove2.me/submissions/c89cc1a8-0b30-43f9-8139-410cbdf100bd

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]























/-- Every actual observed zero-free fibre consists of three-element
supports, each of which avoids zero. -/
theorem p2m_local_zeroFreeFullFibres_support_card_and_zero
    (F : Finset (Finset G))
    (hF : F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))))
    (S : Finset G) (hS : S ∈ F) :
    S.card = 3 ∧ 0 ∉ S := by
  change F ∈ (nonemptyFullFibres : Finset (Finset (Finset G))).image withoutZero at hF
  obtain ⟨K, hK, hKF⟩ := Finset.mem_image.mp hF
  rw [← hKF] at hS
  obtain ⟨hSK, hZero⟩ := Finset.mem_filter.mp hS
  have hAll : K ∈ (allSquareFibres : Finset (Finset (Finset G))) :=
    (Finset.mem_filter.mp hK).1
  obtain ⟨T, _, hTK⟩ := Finset.mem_image.mp hAll
  have hSsq : S ∈ squareFibre T := by
    rw [hTK]
    exact hSK
  exact ⟨((mem_squareFibre T S).mp hSsq).1, hZero⟩




end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (F : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
      (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2) F →
    ∀ (S : Finset.{p2m_u_0} G),
      @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
            (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
          F S →
        And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (Not
            (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) S
              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_0} G
                  (@NegZeroClass.toZero.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_support_card_and_zero

