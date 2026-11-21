-- Prove2me | solution 1 for Kourovka.CentralProductPowers.diagonal_surjective_on_derived
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:40:54.861294+00:00
-- url     : https://prove2.me/submissions/71107699-adbb-4b55-8d57-b9da3a5343ee

import Definitions.Def_Kourovka_PathExpansion
import Definitions.Def_Kourovka_DerivedReduction
import Definitions.Def_Kourovka_CentralProductPowers
import Theorems.Thm_Kourovka_ProductHom_decompose
import Theorems.Thm_Kourovka_ProductPaths_axis_axis_same
import Theorems.Thm_Kourovka_ProductPaths_axis_false
import Theorems.Thm_Kourovka_ProductPaths_axis_true
import Theorems.Thm_Kourovka_ProductPaths_iterateHom_apply
import Theorems.Thm_Kourovka_ProductPaths_path_cons
import Theorems.Thm_Kourovka_ProductPaths_path_nil
import Theorems.Thm_Kourovka_central_map_kills_commutator
attribute [local simp] Kourovka.ProductPaths.axis_axis_same
attribute [local simp] Kourovka.ProductPaths.axis_false
attribute [local simp] Kourovka.ProductPaths.axis_true
attribute [local simp] Kourovka.ProductPaths.iterateHom_apply
attribute [local simp] Kourovka.ProductPaths.path_cons
attribute [local simp] Kourovka.ProductPaths.path_nil



set_option autoImplicit true
open Kourovka Kourovka.CentralProductPowers
open ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.CentralProductPowers
theorem _root_.solution (f : A × B →* A × B)
    (hf : Function.Surjective f)
    (h12 : ∀ b, (f (1, b)).1 ∈ Subgroup.center A)
    (h21 : ∀ a, (f (a, 1)).2 ∈ Subgroup.center B) :
    (∀ y ∈ commutator A, ∃ x ∈ commutator A, (f (x, 1)).1 = y) ∧
    (∀ y ∈ commutator B, ∃ x ∈ commutator B, (f (1, x)).2 = y) := by
  have heq : commutator (A × B) = (commutator A).prod (commutator B) := by
    simpa only [commutator_def, Subgroup.top_prod_top] using
      Subgroup.commutator_prod_prod (⊤ : Subgroup A) ⊤ (⊤ : Subgroup B) ⊤
  have hsurj : ∀ y ∈ commutator (A × B),
      ∃ x ∈ commutator (A × B), f x = y := by
    intro y hy
    have hmap := (derivedSeries_le_map_derivedSeries hf 1) hy
    exact hmap
  constructor
  · intro y hy
    obtain ⟨⟨x, z⟩, hxz, he⟩ := hsurj (y, 1) (by
      rw [heq]
      exact ⟨hy, (commutator B).one_mem⟩)
    rw [heq] at hxz
    have hz : (f (1, z)).1 = 1 := central_map_kills_commutator
      ((MonoidHom.fst A B).comp (ProductHom.right f)) h12 hxz.2
    refine ⟨x, hxz.1, ?_⟩
    have h := congrArg Prod.fst (ProductHom.decompose f x z)
    simp only [he, Prod.fst_mul, ProductHom.left_apply, ProductHom.right_apply, hz, mul_one] at h
    exact h.symm
  · intro y hy
    obtain ⟨⟨x, z⟩, hxz, he⟩ := hsurj (1, y) (by
      rw [heq]
      exact ⟨(commutator A).one_mem, hy⟩)
    rw [heq] at hxz
    have hx : (f (x, 1)).2 = 1 := central_map_kills_commutator
      ((MonoidHom.snd A B).comp (ProductHom.left f)) h21 hxz.1
    refine ⟨z, hxz.2, ?_⟩
    have h := congrArg Prod.snd (ProductHom.decompose f x z)
    simp only [he, Prod.snd_mul, ProductHom.left_apply, ProductHom.right_apply, hx, one_mul] at h
    exact h.symm
end Kourovka.CentralProductPowers
