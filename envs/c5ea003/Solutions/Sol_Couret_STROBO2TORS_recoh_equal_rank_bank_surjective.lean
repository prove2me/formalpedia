-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_equal_rank_bank_surjective
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:40.857807+00:00
-- url     : https://prove2.me/submissions/0c476be6-6d98-42f8-859a-916864e3e543

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
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

/-!
RECOH: the square (k=r) information-set case.
This avoids claiming any selection theorem for k > r.
-/

namespace Couret.STROBO2TORS

/-- If H has 2^r elements and an r-coordinate binary additive bank
is injective, it is surjective. This is the equal-cardinality case
of the information-set problem, NOT the full arbitrary-k case. -/
theorem p2m_local_recoh_equal_rank_bank_surjective
    {H : Type*} [AddCommGroup H] [Fintype H]
    (r : ℕ)
    (hcard : Fintype.card H = 2 ^ r)
    (bank : Fin r → H →+ ZMod 2)
    (hinj : Function.Injective
      (fun a : H => fun i : Fin r => bank i a)) :
    Function.Surjective
      (fun a : H => fun i : Fin r => bank i a) := by
  classical
  have hcodomain :
      Fintype.card (Fin r → ZMod 2) = Fintype.card H := by
    simp [Fintype.card_fun, hcard, ZMod.card]
  exact (Fintype.bijective_iff_injective_and_card
    (fun a : H => fun i : Fin r => bank i a)).2
      ⟨hinj, hcodomain.symm⟩ |>.2

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {H : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} H] [inst_1 : Fintype.{p2m_u_0} H] (r : Nat),
  @Eq.{1} Nat (@Fintype.card.{p2m_u_0} H inst_1)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r) →
    ∀
      (bank :
        Fin r →
          @AddMonoidHom.{p2m_u_0, 0} H (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@AddZeroClass.toAddZero.{p2m_u_0} H
              (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
            (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddMonoidWithOne.toAddMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))),
      (@Function.Injective.{p2m_u_0 + 1, 1} H
          (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun a i =>
          @DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
            (@AddMonoidHom.{p2m_u_0, 0} H (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddZeroClass.toAddZero.{p2m_u_0} H
                (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
              (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddMonoidWithOne.toAddMonoid.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
            H (fun x => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@AddMonoidHom.instFunLike.{p2m_u_0, 0} H
              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddZeroClass.toAddZero.{p2m_u_0} H
                (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
              (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddMonoidWithOne.toAddMonoid.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
            (bank i) a) →
        @Function.Surjective.{p2m_u_0 + 1, 1} H
          (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun a i =>
          @DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
            (@AddMonoidHom.{p2m_u_0, 0} H (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddZeroClass.toAddZero.{p2m_u_0} H
                (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
              (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddMonoidWithOne.toAddMonoid.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
            H (fun x => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@AddMonoidHom.instFunLike.{p2m_u_0, 0} H
              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddZeroClass.toAddZero.{p2m_u_0} H
                (@AddMonoid.toAddZeroClass.{p2m_u_0} H
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))
              (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddMonoidWithOne.toAddMonoid.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
            (bank i) a := @_root_.Couret.STROBO2TORS.p2m_local_recoh_equal_rank_bank_surjective

