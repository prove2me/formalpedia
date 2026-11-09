-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_short_ternary_bank_has_kernel
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:42:29.240194+00:00
-- url     : https://prove2.me/submissions/00008d54-ee7b-47e0-ab7f-7366c161102e

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_short_mod_bank_has_kernel
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









/-- Ternary character restrictions of rank s need at least s
homomorphic probes to have trivial common kernel. -/
theorem p2m_local_recoh_short_ternary_bank_has_kernel
    {A : Type*} [AddCommGroup A] [Fintype A]
    (s k : ℕ)
    (hcard : Fintype.card A = 3 ^ s)
    (hk : k < s)
    (bank : Fin k → A →+ ZMod 3) :
    ∃ a : A, a ≠ 0 ∧ ∀ i : Fin k, bank i a = 0 := by
  exact recoh_short_mod_bank_has_kernel 3 s k (by decide) hcard hk bank

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {A : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} A] [inst_1 : Fintype.{p2m_u_0} A] (s k : Nat),
  @Eq.{1} Nat (@Fintype.card.{p2m_u_0} A inst_1)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) s) →
    @LT.lt.{0} Nat instLTNat k s →
      ∀
        (bank :
          Fin k →
            @AddMonoidHom.{p2m_u_0, 0} A (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@AddZeroClass.toAddZero.{p2m_u_0} A
                (@AddMonoid.toAddZeroClass.{p2m_u_0} A
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))))
              (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@AddMonoidWithOne.toAddMonoid.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))))),
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
            (∀ (i : Fin k),
              @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                  (@AddMonoidHom.{p2m_u_0, 0} A (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@AddZeroClass.toAddZero.{p2m_u_0} A
                      (@AddMonoid.toAddZeroClass.{p2m_u_0} A
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))))
                    (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@AddMonoid.toAddZeroClass.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@AddMonoidWithOne.toAddMonoid.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (@AddGroupWithOne.toAddMonoidWithOne.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (@Ring.toAddGroupWithOne.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))))
                  A (fun x => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@AddMonoidHom.instFunLike.{p2m_u_0, 0} A
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@AddZeroClass.toAddZero.{p2m_u_0} A
                      (@AddMonoid.toAddZeroClass.{p2m_u_0} A
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))))
                    (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@AddMonoid.toAddZeroClass.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@AddMonoidWithOne.toAddMonoid.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (@AddGroupWithOne.toAddMonoidWithOne.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (@Ring.toAddGroupWithOne.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))))
                  (bank i) a)
                (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
                  (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@instMulZeroClassOfSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@CommSemiring.toSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (@CommRing.toCommSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_short_ternary_bank_has_kernel

