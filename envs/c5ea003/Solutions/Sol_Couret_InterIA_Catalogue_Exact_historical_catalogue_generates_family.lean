-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Exact.historical_catalogue_generates_family
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:24.025695+00:00
-- url     : https://prove2.me/submissions/082219a5-5172-4649-afb3-23257c4e8a30

import Aesop
import Definitions.Def_Couret_CyclicCatalogueEquivalence_bddddc095b9c
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_ReferenceCatalogueConverse_0cbe68a31344
import Definitions.Def_Couret_InteriaC4m_265d5cdb2807

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Ambient

















theorem p2m_local_historical_catalogue_generates_family (n : ℕ) (S T : Finset (ZMod n))
    (h : HistoricalCatalogue n S T) : ClassicalFamilyCatalogue n S T := by
  obtain ⟨m,hm,hnm,t,ht,d,b,hd,hb,hn,hb4,u,v,ho⟩ := h
  have ht0 : t+t=0 := by
    rcases ht with rfl|rfl
    · simp
    · calc (m : ZMod n)+m=((2*m : ℕ) : ZMod n) := by simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,two_mul]
           _=0 := by rw [← hnm]; exact ZMod.natCast_self n
  have hdiv : 4*b ∣ n := by rw [hn]; exact ⟨d,by ring⟩
  have hratio : n/(4*b)=d := by
    rw [hn,show 4*(d*b)=(4*b)*d by ring]
    exact Nat.mul_div_cancel_left d (by omega)
  let a : (ZMod n)ˣ := u⁻¹
  let w : ZMod n := -(a : ZMod n)*v
  have hinv (A : Finset (ZMod n)) :
      (A.image (fun z => (u : ZMod n)*z+v)).image (fun z => (a : ZMod n)*z+w)=A := by
    rw [image_image]
    calc A.image (fun z => (a : ZMod n)*((u : ZMod n)*z+v)+w)=A.image id := by
           apply Finset.image_congr
           intro z hz
           change (a : ZMod n)*((u : ZMod n)*z+v)+w=z
           calc _=((a : ZMod n)*(u : ZMod n))*z := by dsimp [w]; ring
                _=z := by dsimp [a]; simp
         _=A := Finset.image_id
  have hshift : (T.image (fun z => z+t)).image (fun z => z+t)=T := by
    simp only [image_image,Function.comp_def,add_assoc,ht0,add_zero,Finset.image_id']
  refine ⟨b,by omega,hdiv,a,w,t,ht0,?_⟩
  rw [hratio]
  rcases ho with ⟨hS,hT⟩|⟨hS,hT⟩
  · left
    constructor
    · rw [← hS]
      exact (hinv S).symm
    · rw [← hT,hinv]
      exact hshift.symm
  · right
    constructor
    · rw [← hS]
      exact (hinv S).symm
    · rw [← hT,hinv]
      exact hshift.symm



end Couret.InterIA.Catalogue.Exact

theorem solution : ∀ (n : Nat) (S T : Finset.{0} (ZMod n)),
  Couret.InterIA.Catalogue.Exact.HistoricalCatalogue n S T →
    Couret.InterIA.Catalogue.Exact.ClassicalFamilyCatalogue n S T := @_root_.Couret.InterIA.Catalogue.Exact.p2m_local_historical_catalogue_generates_family

