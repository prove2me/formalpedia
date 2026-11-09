-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_short_mod_bank_has_kernel
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:28:59.031126+00:00
-- url     : https://prove2.me/submissions/899a0a0c-013c-4bbb-8bed-9c274dd2a23b

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_nonzero_kernel_of_small_codomain
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





/-- If |A| = p^r and k < r, k homomorphic ZMod p probes
have a common nonzero kernel element. -/
theorem p2m_local_recoh_short_mod_bank_has_kernel
    {A : Type*} [AddCommGroup A] [Fintype A]
    (p r k : ℕ) [NeZero p]
    (hp : 1 < p)
    (hcard : Fintype.card A = p ^ r)
    (hk : k < r)
    (bank : Fin k → A →+ ZMod p) :
    ∃ a : A, a ≠ 0 ∧ ∀ i : Fin k, bank i a = 0 := by
  let f : A →+ (Fin k → ZMod p) := recohModBankMap p k bank
  have htarget : Fintype.card (Fin k → ZMod p) = p ^ k := by
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hsmall : Fintype.card (Fin k → ZMod p) < Fintype.card A := by
    rw [htarget, hcard]
    exact Nat.pow_lt_pow_right hp hk
  obtain ⟨a, ha, hker⟩ := recoh_nonzero_kernel_of_small_codomain f hsmall
  refine ⟨a, ha, ?_⟩
  intro i
  have hi := congrArg (fun v : Fin k → ZMod p => v i) hker
  simpa [f, recohModBankMap] using hi





end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {A : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} A] [inst_1 : Fintype.{p2m_u_0} A] (p r k : Nat)
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) p],
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) p →
    @Eq.{1} Nat (@Fintype.card.{p2m_u_0} A inst_1)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid)) p r) →
      @LT.lt.{0} Nat instLTNat k r →
        ∀
          (bank :
            Fin k →
              @AddMonoidHom.{p2m_u_0, 0} A (ZMod p)
                (@AddZeroClass.toAddZero.{p2m_u_0} A
                  (@AddMonoid.toAddZeroClass.{p2m_u_0} A
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))))
                (@AddZeroClass.toAddZero.{0} (ZMod p)
                  (@AddMonoid.toAddZeroClass.{0} (ZMod p)
                    (@AddMonoidWithOne.toAddMonoid.{0} (ZMod p)
                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
                        (@Ring.toAddGroupWithOne.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))))),
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
                @Eq.{1} (ZMod p)
                  (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                    (@AddMonoidHom.{p2m_u_0, 0} A (ZMod p)
                      (@AddZeroClass.toAddZero.{p2m_u_0} A
                        (@AddMonoid.toAddZeroClass.{p2m_u_0} A
                          (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))))
                      (@AddZeroClass.toAddZero.{0} (ZMod p)
                        (@AddMonoid.toAddZeroClass.{0} (ZMod p)
                          (@AddMonoidWithOne.toAddMonoid.{0} (ZMod p)
                            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
                              (@Ring.toAddGroupWithOne.{0} (ZMod p)
                                (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p))))))))
                    A (fun x => ZMod p)
                    (@AddMonoidHom.instFunLike.{p2m_u_0, 0} A (ZMod p)
                      (@AddZeroClass.toAddZero.{p2m_u_0} A
                        (@AddMonoid.toAddZeroClass.{p2m_u_0} A
                          (@SubNegMonoid.toAddMonoid.{p2m_u_0} A
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} A (@AddCommGroup.toAddGroup.{p2m_u_0} A inst)))))
                      (@AddZeroClass.toAddZero.{0} (ZMod p)
                        (@AddMonoid.toAddZeroClass.{0} (ZMod p)
                          (@AddMonoidWithOne.toAddMonoid.{0} (ZMod p)
                            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
                              (@Ring.toAddGroupWithOne.{0} (ZMod p)
                                (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p))))))))
                    (bank i) a)
                  (@OfNat.ofNat.{0} (ZMod p) (nat_lit 0)
                    (@Zero.toOfNat0.{0} (ZMod p)
                      (@MulZeroClass.toZero.{0} (ZMod p)
                        (@instMulZeroClassOfSemiring.{0} (ZMod p)
                          (@CommSemiring.toSemiring.{0} (ZMod p)
                            (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_short_mod_bank_has_kernel

