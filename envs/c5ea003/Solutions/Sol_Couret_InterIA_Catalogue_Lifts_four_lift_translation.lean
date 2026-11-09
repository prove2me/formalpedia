-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Lifts.four_lift_translation
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:24.467835+00:00
-- url     : https://prove2.me/submissions/c08123fa-25c9-41aa-81a6-4b22f447ddc9

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







theorem p2m_local_four_lift_translation (m : ℕ) (S T : Finset (ZMod (2*m)))
    (h : FourLift m S T) : FourTranslated m S T := by
  obtain ⟨a,r,c,d,hr,hc,hd,hS,hT⟩ := h
  have hc' : c-a=2 • r ∨ c-a=6 • r := by
    rcases hc with hc|hc
    · left; rw [hc]; abel
    · right; rw [hc]; abel
  have hd' : d-a=3 • r ∨ d-a=7 • r := by
    rcases hd with hd|hd
    · left; rw [hd]; abel
    · right; rw [hd]; abel
  have h0 : a+(-a)=0 := by abel
  have h1 : a+r+(-a)=r := by abel
  have h4 : a+4 • r+(-a)=4 • r := by abel
  have h5 : a+5 • r+(-a)=5 • r := by abel
  refine ⟨-a,r,c-a,d-a,hr,hc',hd',?_,?_⟩
  · rw [hS]
    simp only [image_insert,image_singleton,h0,h4,sub_eq_add_neg]
  · rw [hT]
    simp only [image_insert,image_singleton,h1,h5,sub_eq_add_neg]

end Couret.InterIA.Catalogue.Lifts

theorem solution : ∀ (m : Nat)
  (S T :
    Finset.{0}
      (ZMod
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))),
  Couret.InterIA.Catalogue.Lifts.FourLift m S T → Couret.InterIA.Catalogue.Lifts.FourTranslated m S T := @_root_.Couret.InterIA.Catalogue.Lifts.p2m_local_four_lift_translation

