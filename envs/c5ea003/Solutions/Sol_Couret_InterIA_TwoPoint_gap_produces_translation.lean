-- Prove2me | solution 1 for Couret.InterIA.TwoPoint.gap_produces_translation
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:31:00.620985+00:00
-- url     : https://prove2.me/submissions/5ae7cf1b-fc27-4ee7-9726-50813e425aa0

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





























theorem p2m_local_gap_produces_translation (a b c d : G)
    (hgap : d-c=b-a ∨ c-d=b-a) :
    ∃ t : G, ({a,b} : Finset G).image (fun x => x+t)=({c,d} : Finset G) := by
  rcases hgap with hgap|hgap
  · refine ⟨c-a,?_⟩
    have ha : a+(c-a)=c := by abel
    have hb : b+(c-a)=d := by
      calc b+(c-a)=(b-a)+c := by abel
           _=(d-c)+c := by rw [hgap]
           _=d := by abel
    simp [ha,hb]
  · refine ⟨d-a,?_⟩
    have ha : a+(d-a)=d := by abel
    have hb : b+(d-a)=c := by
      calc b+(d-a)=(b-a)+d := by abel
           _=(c-d)+d := by rw [hgap]
           _=c := by abel
    simp [ha,hb,Finset.pair_comm]





end Couret.InterIA.TwoPoint

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (a b c d : G),
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
          b a)) →
    @Exists.{p2m_u_0 + 1} G fun t =>
      @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
        (@Finset.image.{p2m_u_0, p2m_u_0} G G inst_1
          (fun x =>
            @HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              x t)
          (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) a
            (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G) b)))
        (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) c
          (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G) d)) := @_root_.Couret.InterIA.TwoPoint.p2m_local_gap_produces_translation

