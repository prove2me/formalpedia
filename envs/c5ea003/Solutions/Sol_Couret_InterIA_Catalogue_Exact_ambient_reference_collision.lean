-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Exact.ambient_reference_collision
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:42.872465+00:00
-- url     : https://prove2.me/submissions/b7c2911b-7c18-4ef6-a4d6-9fae0be7ba78

import Definitions.Def_Couret_ReferenceCatalogueConverse_0cbe68a31344
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
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_affine_equivalent_symm
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_common_affine_equivalent_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_dilated_reference_collision
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_square_pair_affine_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Parameters_affine_image_card
import Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Arithmetic Couret.InterIA.Catalogue.Quarter.Ambient
open Couret.InterIA.Catalogue.Quarter.AffineCriterion Couret.InterIA.Catalogue.AffineTransport







theorem four_collision_affine_iff {n : ℕ} (S T : Finset (ZMod n))
    (u : (ZMod n)ˣ) (v : ZMod n) :
    FourCollision (S.image (fun x => (u : ZMod n)*x+v))
      (T.image (fun x => (u : ZMod n)*x+v)) ↔ FourCollision S T := by
  simp only [FourCollision,Couret.InterIA.Catalogue.Parameters.affine_image_card,
    square_pair_affine_iff,common_affine_equivalent_iff]

theorem four_collision_swap {n : ℕ} (S T : Finset (ZMod n)) :
    FourCollision S T ↔ FourCollision T S := by
  constructor
  · rintro ⟨hS,hT,hsq,hna⟩
    exact ⟨hT,hS,fun z => (hsq z).symm,fun he => hna (affine_equivalent_symm T S he)⟩
  · rintro ⟨hT,hS,hsq,hna⟩
    exact ⟨hS,hT,fun z => (hsq z).symm,fun he => hna (affine_equivalent_symm S T he)⟩







theorem p2m_local_ambient_reference_collision (n : ℕ) (S T : Finset (ZMod n))
    (h : AmbientReferenceForm n S T) : FourCollision S T := by
  obtain ⟨d,b,hd,hb,hn,hm,u,v,ho⟩ := h
  have href := dilated_reference_collision n d b hn hd hb hm
  apply (four_collision_affine_iff S T u v).mp
  rcases ho with ⟨hS,hT⟩|⟨hS,hT⟩
  · rw [hS,hT]
    exact href
  · rw [hS,hT]
    exact (four_collision_swap _ _).mp href

end Couret.InterIA.Catalogue.Exact

theorem solution : ∀ (n : Nat) (S T : Finset.{0} (ZMod n)),
  Couret.InterIA.Catalogue.Quarter.Ambient.AmbientReferenceForm n S T →
    @Couret.InterIA.Catalogue.Exact.FourCollision n S T := @_root_.Couret.InterIA.Catalogue.Exact.p2m_local_ambient_reference_collision

