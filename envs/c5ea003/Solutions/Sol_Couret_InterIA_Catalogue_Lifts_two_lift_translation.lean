-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Lifts.two_lift_translation
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:08.6612+00:00
-- url     : https://prove2.me/submissions/aea6ea61-0cce-48ae-adf6-43e30b10a9b8

import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_OrbitLiftModels_210387863d55

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Lifts
open Finset





theorem p2m_local_two_lift_translation (m : ℕ) (S T : Finset (ZMod (2*m)))
    (h : TwoLift m S T) : TwoTranslated m S T := by
  obtain ⟨a,c,r,hr,hS,hT⟩ := h
  have h0 : c+(-c)=0 := by abel
  have h1 : c+r+(-c)=r := by abel
  have h2 : a+2 • r+(-c)=a-c+2 • r := by abel
  have ha : a+(-c)=a-c := by abel
  have ha1 : a+r+(-c)=a-c+r := by abel
  have ha3 : a+3 • r+(-c)=a-c+3 • r := by abel
  refine ⟨-c,a-c,r,hr,?_,?_⟩
  · rw [hS]
    simp only [image_insert,image_singleton,h0,h1,h2,ha]
  · rw [hT]
    simp only [image_insert,image_singleton,h0,h1,ha1,ha3]



end Couret.InterIA.Catalogue.Lifts

theorem solution : ∀ (m : Nat)
  (S T :
    Finset.{0}
      (ZMod
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))),
  Couret.InterIA.Catalogue.Lifts.TwoLift m S T → Couret.InterIA.Catalogue.Lifts.TwoTranslated m S T := @_root_.Couret.InterIA.Catalogue.Lifts.p2m_local_two_lift_translation

