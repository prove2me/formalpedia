-- Prove2me | solution 1 for Couret.InterIA.L4.normal_form_identity
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:31:11.226818+00:00
-- url     : https://prove2.me/submissions/5cac7cf7-7ac9-4e8e-aa06-af18ff8e29c5

import Definitions.Def_Couret_L4Foundations_a0fb4bb69682
import Mathlib.Data.Finset.Insert
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

set_option autoImplicit false

namespace Couret.InterIA.L4

section Cyclic







end Cyclic

section Rectangle
variable {G : Type*} [AddCommGroup G] [DecidableEq G]



end Rectangle



section Algebra
variable {R : Type*} [CommRing R]







theorem p2m_local_normal_form_identity (H a b c : R) (hH : H*H=1) :
    (c+(1+H)*a)^2-(c+(1+H)*b)^2 =
      2*(1+H)*(a-b)*(c+a+b) := by
  have hs := antipodal_square H hH
  calc
    _ = 2*c*(1+H)*(a-b) + ((1+H)*(1+H))*(a*a-b*b) := by ring
    _ = _ := by rw [hs]; ring

end Algebra

section IntegerCoefficients
variable {α : Type*}





end IntegerCoefficients

end Couret.InterIA.L4

universe p2m_u_0
theorem solution : ∀ {R : Type p2m_u_0} [inst : CommRing.{p2m_u_0} R] (H a b c : R),
  @Eq.{p2m_u_0 + 1} R
      (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
        (@instHMul.{p2m_u_0} R
          (@Distrib.toMul.{p2m_u_0} R
            (@instDistribOfSemiring.{p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
        H H)
      (@OfNat.ofNat.{p2m_u_0} R (nat_lit 1)
        (@One.toOfNat1.{p2m_u_0} R
          (@AddMonoidWithOne.toOne.{p2m_u_0} R
            (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R
              (@Ring.toAddGroupWithOne.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst)))))) →
    @Eq.{p2m_u_0 + 1} R
      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
        (@instHSub.{p2m_u_0} R
          (@SubNegMonoid.toSub.{p2m_u_0} R
            (@AddGroup.toSubNegMonoid.{p2m_u_0} R
              (@AddGroupWithOne.toAddGroup.{p2m_u_0} R
                (@Ring.toAddGroupWithOne.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst))))))
        (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} R Nat R
          (@instHPow.{p2m_u_0, 0} R Nat
            (@Monoid.toPow.{p2m_u_0} R
              (@Semiring.toMonoid.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
            (@instHAdd.{p2m_u_0} R
              (@Distrib.toAdd.{p2m_u_0} R
                (@instDistribOfSemiring.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
            c
            (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
              (@instHMul.{p2m_u_0} R
                (@Distrib.toMul.{p2m_u_0} R
                  (@instDistribOfSemiring.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
                (@instHAdd.{p2m_u_0} R
                  (@Distrib.toAdd.{p2m_u_0} R
                    (@instDistribOfSemiring.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
                (@OfNat.ofNat.{p2m_u_0} R (nat_lit 1)
                  (@One.toOfNat1.{p2m_u_0} R
                    (@AddMonoidWithOne.toOne.{p2m_u_0} R
                      (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R
                        (@Ring.toAddGroupWithOne.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst))))))
                H)
              a))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HPow.hPow.{p2m_u_0, 0, p2m_u_0} R Nat R
          (@instHPow.{p2m_u_0, 0} R Nat
            (@Monoid.toPow.{p2m_u_0} R
              (@Semiring.toMonoid.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
            (@instHAdd.{p2m_u_0} R
              (@Distrib.toAdd.{p2m_u_0} R
                (@instDistribOfSemiring.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
            c
            (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
              (@instHMul.{p2m_u_0} R
                (@Distrib.toMul.{p2m_u_0} R
                  (@instDistribOfSemiring.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
                (@instHAdd.{p2m_u_0} R
                  (@Distrib.toAdd.{p2m_u_0} R
                    (@instDistribOfSemiring.{p2m_u_0} R
                      (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
                (@OfNat.ofNat.{p2m_u_0} R (nat_lit 1)
                  (@One.toOfNat1.{p2m_u_0} R
                    (@AddMonoidWithOne.toOne.{p2m_u_0} R
                      (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R
                        (@Ring.toAddGroupWithOne.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst))))))
                H)
              b))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
        (@instHMul.{p2m_u_0} R
          (@Distrib.toMul.{p2m_u_0} R
            (@instDistribOfSemiring.{p2m_u_0} R
              (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
        (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
          (@instHMul.{p2m_u_0} R
            (@Distrib.toMul.{p2m_u_0} R
              (@instDistribOfSemiring.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
          (@HMul.hMul.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
            (@instHMul.{p2m_u_0} R
              (@Distrib.toMul.{p2m_u_0} R
                (@instDistribOfSemiring.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
            (@OfNat.ofNat.{p2m_u_0} R (nat_lit 2)
              (@instOfNatAtLeastTwo.{p2m_u_0} R (nat_lit 2)
                (@AddMonoidWithOne.toNatCast.{p2m_u_0} R
                  (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R
                    (@Ring.toAddGroupWithOne.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst))))
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
              (@instHAdd.{p2m_u_0} R
                (@Distrib.toAdd.{p2m_u_0} R
                  (@instDistribOfSemiring.{p2m_u_0} R
                    (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
              (@OfNat.ofNat.{p2m_u_0} R (nat_lit 1)
                (@One.toOfNat1.{p2m_u_0} R
                  (@AddMonoidWithOne.toOne.{p2m_u_0} R
                    (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_0} R
                      (@Ring.toAddGroupWithOne.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst))))))
              H))
          (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
            (@instHSub.{p2m_u_0} R
              (@SubNegMonoid.toSub.{p2m_u_0} R
                (@AddGroup.toSubNegMonoid.{p2m_u_0} R
                  (@AddGroupWithOne.toAddGroup.{p2m_u_0} R
                    (@Ring.toAddGroupWithOne.{p2m_u_0} R (@CommRing.toRing.{p2m_u_0} R inst))))))
            a b))
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
          (@instHAdd.{p2m_u_0} R
            (@Distrib.toAdd.{p2m_u_0} R
              (@instDistribOfSemiring.{p2m_u_0} R
                (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} R R R
            (@instHAdd.{p2m_u_0} R
              (@Distrib.toAdd.{p2m_u_0} R
                (@instDistribOfSemiring.{p2m_u_0} R
                  (@CommSemiring.toSemiring.{p2m_u_0} R (@CommRing.toCommSemiring.{p2m_u_0} R inst)))))
            c a)
          b)) := @_root_.Couret.InterIA.L4.p2m_local_normal_form_identity

