-- Prove2me | solution 1 for Couret.InterIA.TwoPoint.distinct_doubles_gap
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:30:50.320384+00:00
-- url     : https://prove2.me/submissions/50bdd9a6-9805-494b-a01d-959aef457d1a

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



















theorem p2m_local_distinct_doubles_gap (a b c d : G) (hab : a ≠ b)
    (hd : a+a ≠ b+b)
    (heq : ∀ z, pairCoeff a b z=pairCoeff c d z) :
    d-c=b-a ∨ c-d=b-a := by
  have hp := heq (a+a)
  rw [pair_coeff_at_double_distinct a b hab hd] at hp
  have hc : c+c=a+a ∨ d+d=a+a := by
    by_contra hn
    have hnc : c+c ≠ a+a := by tauto
    have hnd : d+d ≠ a+a := by tauto
    simp only [pairCoeff,if_neg hnc,if_neg hnd,zero_add] at hp
    split_ifs at hp <;> omega
  rcases hc with hc|hd'
  · have hs := matched_double_forces_center a b c d hab hd heq hc
    left
    calc d-c=(c+d)-(c+c) := by abel
         _=(a+b)-(a+a) := by rw [hs,hc]
         _=b-a := by abel
  · have heq' : ∀ z, pairCoeff a b z=pairCoeff d c z := by
      intro z
      exact (heq z).trans (pair_coeff_comm c d z)
    have hs := matched_double_forces_center a b d c hab hd heq' hd'
    right
    calc c-d=(d+c)-(d+d) := by abel
         _=(a+b)-(a+a) := by rw [hs,hd']
         _=b-a := by abel















end Couret.InterIA.TwoPoint

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (a b c d : G),
  @Ne.{p2m_u_0 + 1} G a b →
    @Ne.{p2m_u_0 + 1} G
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
              b a)) := @_root_.Couret.InterIA.TwoPoint.p2m_local_distinct_doubles_gap

