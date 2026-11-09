-- Prove2me | solution 1 for Couret.InterIA.TwoPoint.equal_doubles_gap
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:30:55.72658+00:00
-- url     : https://prove2.me/submissions/ee7becb5-29ef-4eb2-be6c-7ab9c03acd6f

import Definitions.Def_Couret_TwoPointCollision_eefa36a5b454
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.TwoPoint
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

























theorem p2m_local_equal_doubles_gap (a b c d : G) (hab : a ≠ b) (hcd : c ≠ d)
    (hd : a+a=b+b)
    (heq : ∀ z, pairCoeff a b z=pairCoeff c d z) :
    d-c=b-a ∨ c-d=b-a := by
  have hD := equal_doubles_transfer a b c d hcd hd heq
  have hp1 : pairCoeff a b (c+c)=2 := by
    rw [heq,pair_coeff_at_double_equal c d hcd hD]
  have hp2 : pairCoeff a b (c+d)=2 := by rw [heq,pair_coeff_at_sum c d hcd]
  rcases equal_doubles_positions a b (c+c) hd hp1 with hc|hc <;>
    rcases equal_doubles_positions a b (c+d) hd hp2 with hs|hs
  · exact False.elim (pair_sum_ne_left_double c d hcd (hs.symm.trans hc))
  · left
    calc d-c=(c+d)-(c+c) := by abel
         _=(a+b)-(a+a) := by rw [← hs,← hc]
         _=b-a := by abel
  · right
    calc c-d=(c+c)-(c+d) := by abel
         _=(a+b)-(a+a) := by rw [← hc,← hs]
         _=b-a := by abel
  · exact False.elim (pair_sum_ne_left_double c d hcd (hs.symm.trans hc))









end Couret.InterIA.TwoPoint

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (a b c d : G),
  @Ne.{p2m_u_0 + 1} G a b →
    @Ne.{p2m_u_0 + 1} G c d →
      @Eq.{p2m_u_0 + 1} G
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            a a)
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            b b) →
        (∀ (z : G),
            @Eq.{1} Nat (@Couret.InterIA.TwoPoint.pairCoeff.{p2m_u_0} G inst inst_1 a b z)
              (@Couret.InterIA.TwoPoint.pairCoeff.{p2m_u_0} G inst inst_1 c d z)) →
          Or
            (@Eq.{p2m_u_0 + 1} G
              (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHSub.{p2m_u_0} G
                  (@SubNegMonoid.toSub.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                d c)
              (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHSub.{p2m_u_0} G
                  (@SubNegMonoid.toSub.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                b a))
            (@Eq.{p2m_u_0 + 1} G
              (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHSub.{p2m_u_0} G
                  (@SubNegMonoid.toSub.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                c d)
              (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHSub.{p2m_u_0} G
                  (@SubNegMonoid.toSub.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                b a)) := @_root_.Couret.InterIA.TwoPoint.p2m_local_equal_doubles_gap

