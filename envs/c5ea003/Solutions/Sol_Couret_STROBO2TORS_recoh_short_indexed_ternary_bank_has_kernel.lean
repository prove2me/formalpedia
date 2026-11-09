-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_short_indexed_ternary_bank_has_kernel
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:43:38.251186+00:00
-- url     : https://prove2.me/submissions/21a6c38a-3edc-4701-b797-6e0dd31ca540

import Aesop
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_nonzero_kernel_of_small_codomain
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-!
RECOH / STROBO: binary pivot mask counting and ternary subbank kernels.

Conditional interface for the missing mixed-rank selection step.
A surjective rank-r family of binary probes lets one force r signs
simultaneously, leaving fewer than s neutral probes if k < r+s.

The UNCONDITIONAL existence of the pivot family for every full-rank
binary restriction bank is not claimed in this file.
-/

namespace Couret.STROBO2TORS



/-- The common-kernel lemma works for an arbitrarily indexed family of
ternary additive restrictions, not just one enumerated by Fin t.
This lets the binary-zero coordinates serve directly as the index type. -/
theorem p2m_local_recoh_short_indexed_ternary_bank_has_kernel
    {A I : Type*}
    [AddCommGroup A] [Fintype A]
    [Fintype I]
    (s : ℕ) (hcard : Fintype.card A = 3 ^ s)
    (hI : Fintype.card I < s)
    (bank : I → A →+ ZMod 3) :
    ∃ a : A, a ≠ 0 ∧ ∀ i : I, bank i a = 0 := by
  classical
  let f : A →+ (I → ZMod 3) :=
    { toFun := fun a i => bank i a
      map_zero' := by
        funext i
        simp
      map_add' := by
        intro a b
        funext i
        simp }
  have hsmall : Fintype.card (I → ZMod 3) < Fintype.card A := by
    rw [Fintype.card_fun, hcard, ZMod.card]
    exact Nat.pow_lt_pow_right (by decide : 1 < 3) hI
  obtain ⟨a, ha, hker⟩ :=
    recoh_nonzero_kernel_of_small_codomain f hsmall
  refine ⟨a, ha, ?_⟩
  intro i
  have hi := congrArg (fun v : I → ZMod 3 => v i) hker
  simpa [f] using hi

end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {A : Type p2m_u_0} {I : Type p2m_u_1} [inst : AddCommGroup.{p2m_u_0} A] [inst_1 : Fintype.{p2m_u_0} A]
  [inst_2 : Fintype.{p2m_u_1} I] (s : Nat),
  @Eq.{1} Nat (@Fintype.card.{p2m_u_0} A inst_1)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) s) →
    @LT.lt.{0} Nat instLTNat (@Fintype.card.{p2m_u_1} I inst_2) s →
      ∀
        (bank :
          I →
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
            (∀ (i : I),
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
                            (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_short_indexed_ternary_bank_has_kernel

