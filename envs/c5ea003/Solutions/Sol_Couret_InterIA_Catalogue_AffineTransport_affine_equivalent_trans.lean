-- Prove2me | solution 1 for Couret.InterIA.Catalogue.AffineTransport.affine_equivalent_trans
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:48:11.040379+00:00
-- url     : https://prove2.me/submissions/d72ff8cb-9980-40ab-9000-903a38a76aeb

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

theorem p2m_local_affine_equivalent_trans {n : ℕ} (S T U : Finset (ZMod n))
    (hST : AffineEquivalent S T) (hTU : AffineEquivalent T U) : AffineEquivalent S U := by
  obtain ⟨u,v,huv⟩ := hST
  obtain ⟨a,b,hab⟩ := hTU
  refine ⟨a*u,(a : ZMod n)*v+b,?_⟩
  calc
    S.image (fun z => (↑(a*u) : ZMod n)*z+((a : ZMod n)*v+b))=
        (S.image (fun z => (u : ZMod n)*z+v)).image (fun z => (a : ZMod n)*z+b) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro z hz
      simp only [Units.val_mul,Function.comp_apply]
      ring
    _=U := by rw [huv,hab]











end Couret.InterIA.Catalogue.AffineTransport

theorem solution : ∀ {n : Nat} (S T U : Finset.{0} (ZMod n)),
  @Couret.InterIA.NormalForm.AffineEquivalent n S T →
    @Couret.InterIA.NormalForm.AffineEquivalent n T U → @Couret.InterIA.NormalForm.AffineEquivalent n S U := @_root_.Couret.InterIA.Catalogue.AffineTransport.p2m_local_affine_equivalent_trans

