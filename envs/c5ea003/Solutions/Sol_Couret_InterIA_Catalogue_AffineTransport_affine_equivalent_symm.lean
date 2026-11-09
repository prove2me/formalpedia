-- Prove2me | solution 1 for Couret.InterIA.Catalogue.AffineTransport.affine_equivalent_symm
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:47:47.511588+00:00
-- url     : https://prove2.me/submissions/ab22bfc5-5bb9-442e-9952-2d3c3add301d

import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Definitions.Def_Couret_AffineParameterControls_321393084939

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.AffineTransport
open Finset Couret.InterIA.NormalForm



theorem p2m_local_affine_equivalent_symm {n : ℕ} (S T : Finset (ZMod n))
    (h : AffineEquivalent S T) : AffineEquivalent T S := by
  obtain ⟨u,v,h⟩ := h
  refine ⟨u⁻¹,-(↑(u⁻¹) : ZMod n)*v,?_⟩
  rw [← h,Finset.image_image]
  calc
    S.image (fun z => (↑(u⁻¹) : ZMod n)*((u : ZMod n)*z+v)+ -(↑(u⁻¹) : ZMod n)*v)=S.image id := by
      apply Finset.image_congr
      intro z hz
      change (↑(u⁻¹) : ZMod n)*((u : ZMod n)*z+v)+ -(↑(u⁻¹) : ZMod n)*v=z
      calc _=((↑(u⁻¹) : ZMod n)*(u : ZMod n))*z := by ring
           _=z := by simp
    _=S := Finset.image_id









end Couret.InterIA.Catalogue.AffineTransport

theorem solution : ∀ {n : Nat} (S T : Finset.{0} (ZMod n)),
  @Couret.InterIA.NormalForm.AffineEquivalent n S T → @Couret.InterIA.NormalForm.AffineEquivalent n T S := @_root_.Couret.InterIA.Catalogue.AffineTransport.p2m_local_affine_equivalent_symm

