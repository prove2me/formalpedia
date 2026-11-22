-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CommutatorModule.finite_normal_generators_of_kernel_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:57:14.204296+00:00
-- url     : https://prove2.me/submissions/f85fd646-0842-4935-99fa-d657ca327e53

import Definitions.Def_Kourovka_Modules_CommutatorModule
import Definitions.Def_Kourovka_Presentations_KernelGenerators

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {E G : Type} [Group E] [Group G]
namespace Kourovka.MetabelianEnumeration.CommutatorModule
theorem _root_.solution
    (f : E →* G) (hf : Function.Surjective f)
    (N : Subgroup E) [N.Normal] (M : Subgroup G) [M.Normal]
    (e : N ≃* M) (he : ∀ x : N, f x.val = (e x).val)
    (hM : ∃ s : Finset G, Subgroup.normalClosure (s : Set G) = M) :
    ∃ s : Finset N, Subgroup.normalClosure (Subtype.val '' (s : Set N)) = N := by
  classical
  obtain ⟨s, hs⟩ := hM
  have hsm (g : s) : g.val ∈ M := by
    rw [← hs]
    exact Subgroup.subset_normalClosure g.property
  let gen : s → N := fun g => e.symm ⟨g.val, hsm g⟩
  let t : Finset N := Finset.univ.image gen
  have hgen (g : s) : f (gen g).val = g.val := by
    rw [he]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨g.val, hsm g⟩)
  have himage : f '' (Subtype.val '' (t : Set N)) = (s : Set G) := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hy
      rw [hgen]
      exact g.property
    · intro hx
      refine ⟨(gen ⟨x, hx⟩).val, ⟨gen ⟨x, hx⟩, ?_, rfl⟩, hgen ⟨x, hx⟩⟩
      exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
  let C := Subgroup.normalClosure (Subtype.val '' (t : Set N))
  have hCN : C ≤ N := Subgroup.normalClosure_le_normal (by
    rintro _ ⟨x, _, rfl⟩
    exact x.property)
  have hmap : C.map f = M := by
    change (Subgroup.normalClosure _).map f = M
    rw [Subgroup.map_normalClosure _ f hf, himage, hs]
  refine ⟨t, le_antisymm hCN ?_⟩
  intro x hx
  have hfx : f x ∈ C.map f := by
    rw [hmap, he ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  obtain ⟨y, hy, hyx⟩ := hfx
  have heq : (⟨y, hCN hy⟩ : N) = ⟨x, hx⟩ := e.injective (by
    apply Subtype.ext
    rw [← he, ← he]
    exact hyx)
  have hyx' : y = x := congrArg Subtype.val heq
  simpa only [← hyx'] using hy
end Kourovka.MetabelianEnumeration.CommutatorModule
