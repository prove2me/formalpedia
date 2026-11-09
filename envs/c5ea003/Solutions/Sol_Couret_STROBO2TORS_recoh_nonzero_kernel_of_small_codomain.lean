-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_nonzero_kernel_of_small_codomain
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:14.364252+00:00
-- url     : https://prove2.me/submissions/ae880353-cfc7-402b-9869-34a0cdbe26b5

import Aesop
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

/-!
RECOH: finite character rank kernel bound.

For a finite additive group A of cardinal p^r and any list of k < r
additive probes valued in ZMod p, a nonzero element lies in their
common kernel. This is a group-homomorphism statement, not merely
a pigeonhole bound on unstructured binary or ternary words.

Scope boundary: this covers the common-kernel case of the
lower bound. It does NOT build the mixed order-two/order-three
mask for k between r and r+s, nor construct the upper bank.
-/

namespace Couret.STROBO2TORS

/-- A homomorphism into a strictly smaller finite additive group has
a nonzero kernel element. -/
theorem p2m_local_recoh_nonzero_kernel_of_small_codomain
    {A B : Type*}
    [AddCommGroup A] [Fintype A]
    [AddCommGroup B] [Fintype B]
    (f : A →+ B)
    (hsmall : Fintype.card B < Fintype.card A) :
    ∃ a : A, a ≠ 0 ∧ f a = 0 := by
  classical
  by_contra hnone
  have hinj : Function.Injective (fun a : A => f a) := by
    intro x y heq
    by_contra hxy
    have hne : x - y ≠ (0 : A) := sub_ne_zero.mpr hxy
    have hker : f (x - y) = 0 := by
      simpa only [map_sub, sub_self] using congrArg (fun z : B => z - f y) heq
    exact hnone ⟨x - y, hne, hker⟩
  exact (Fintype.not_injective_of_card_lt (fun a : A => f a) hsmall) hinj









end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {A : Type p2m_u_0} {B : Type p2m_u_1} [inst : AddCommGroup.{p2m_u_0} A] [inst_1 : Fintype.{p2m_u_0} A]
  [inst_2 : AddCommGroup.{p2m_u_1} B] [inst_3 : Fintype.{p2m_u_1} B]
  (f :
    @AddMonoidHom.{p2m_u_0, p2m_u_1} A B
      (@AddZeroClass.toAddZero.{p2m_u_0} A
        (@AddMonoid.toAddZeroClass.{p2m_u_0} A
          (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
            (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))))
      (@AddZeroClass.toAddZero.{p2m_u_1} B
        (@AddMonoid.toAddZeroClass.{p2m_u_1} B
          (@SubNegMonoid.toAddMonoid.{p2m_u_1} B
            (@AddGroup.toSubNegMonoid.{p2m_u_1} B (@AddCommGroup.toAddGroup.{p2m_u_1} B inst_2)))))),
  @LT.lt.{0} Nat instLTNat (@Fintype.card.{p2m_u_1} B inst_3) (@Fintype.card.{p2m_u_0} A inst_1) →
    @Exists.{p2m_u_0 + 1} A fun a =>
      And
        (@Ne.{p2m_u_0 + 1} A a
          (@OfNat.ofNat.{p2m_u_0} A (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} A
              (@NegZeroClass.toZero.{p2m_u_0} A
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} A
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} A
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} A
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} A inst))))))))
        (@Eq.{p2m_u_1 + 1} B
          (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
            (@AddMonoidHom.{p2m_u_0, p2m_u_1} A B
              (@AddZeroClass.toAddZero.{p2m_u_0} A
                (@AddMonoid.toAddZeroClass.{p2m_u_0} A
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))))
              (@AddZeroClass.toAddZero.{p2m_u_1} B
                (@AddMonoid.toAddZeroClass.{p2m_u_1} B
                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} B
                    (@AddGroup.toSubNegMonoid.{p2m_u_1} B (@AddCommGroup.toAddGroup.{p2m_u_1} B inst_2))))))
            A (fun x => B)
            (@AddMonoidHom.instFunLike.{p2m_u_0, p2m_u_1} A B
              (@AddZeroClass.toAddZero.{p2m_u_0} A
                (@AddMonoid.toAddZeroClass.{p2m_u_0} A
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))))
              (@AddZeroClass.toAddZero.{p2m_u_1} B
                (@AddMonoid.toAddZeroClass.{p2m_u_1} B
                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} B
                    (@AddGroup.toSubNegMonoid.{p2m_u_1} B (@AddCommGroup.toAddGroup.{p2m_u_1} B inst_2))))))
            f a)
          (@OfNat.ofNat.{p2m_u_1} B (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_1} B
              (@NegZeroClass.toZero.{p2m_u_1} B
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_1} B
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_1} B
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_1} B
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_1} B inst_2)))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_nonzero_kernel_of_small_codomain

