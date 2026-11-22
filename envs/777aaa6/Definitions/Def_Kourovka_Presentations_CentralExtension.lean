-- Prove2me | Definitions.Def_Kourovka_Presentations_CentralExtension
-- name    : Kourovka_Presentations_CentralExtension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:41:07.110882+00:00
-- url     : https://prove2.me/theorems/545dd705-10d7-4020-a344-f0e71be1ae1d
-- title:
--   Central Extension
-- statement:
--   Definitions and structural lemmas for Central Extension, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/CentralExtension.lean

import Definitions.Def_Kourovka_Presentations_Presentations
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.CentralExtension
variable {α β : Type} [Fintype α] [Fintype β]
abbrev relSet (R : List (FreeGroup α)) : Set (FreeGroup α) := {r | r ∈ R}
noncomputable def combinedRelations (R : List (FreeGroup α))
    (S : List (FreeGroup β)) (correction : FreeGroup α → FreeGroup β) :
    List (FreeGroup (α ⊕ β)) :=
  R.map (fun r => FreeGroup.map Sum.inl r * (FreeGroup.map Sum.inr (correction r))⁻¹) ++
  S.map (FreeGroup.map Sum.inr) ++
  (Finset.univ : Finset (β × (α ⊕ β))).toList.map
    (fun p => ⁅FreeGroup.of (Sum.inr p.1 : α ⊕ β), FreeGroup.of p.2⁆)
abbrev Combined (R : List (FreeGroup α)) (S : List (FreeGroup β))
    (correction : FreeGroup α → FreeGroup β) :=
  PresentedGroup (relSet (combinedRelations R S correction))
theorem combined_kernel_relation (R : List (FreeGroup α)) (S : List (FreeGroup β))
    (c : FreeGroup α → FreeGroup β) (s : FreeGroup β) (hs : s ∈ S) :
    PresentedGroup.mk (relSet (combinedRelations R S c)) (FreeGroup.map Sum.inr s) = 1 := by
  apply PresentedGroup.one_of_mem
  simp only [relSet, Set.mem_setOf_eq, combinedRelations, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨s, hs, rfl⟩)
theorem combined_generator_commute (R : List (FreeGroup α)) (S : List (FreeGroup β))
    (c : FreeGroup α → FreeGroup β) (b : β) (x : α ⊕ β) :
    Commute (PresentedGroup.of (rels := relSet (combinedRelations R S c)) (Sum.inr b))
      (PresentedGroup.of x) := by
  apply commutatorElement_eq_one_iff_commute.mp
  change ⁅PresentedGroup.mk _ (FreeGroup.of (Sum.inr b)),
    PresentedGroup.mk _ (FreeGroup.of x)⁆ = 1
  rw [← map_commutatorElement]
  apply PresentedGroup.one_of_mem
  simp only [relSet, Set.mem_setOf_eq, combinedRelations, List.mem_append, List.mem_map]
  exact Or.inr ⟨(b, x), by simp, rfl⟩
theorem combined_generator_central (R : List (FreeGroup α)) (S : List (FreeGroup β))
    (c : FreeGroup α → FreeGroup β) (b : β) :
    PresentedGroup.of (rels := relSet (combinedRelations R S c)) (Sum.inr b) ∈
      Subgroup.center (Combined R S c) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  have h : g ∈ Subgroup.centralizer
      {PresentedGroup.of (rels := relSet (combinedRelations R S c)) (Sum.inr b)} := by
    apply PresentedGroup.generated_by
    intro x
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact (combined_generator_commute R S c b x).eq
  exact (show PresentedGroup.of (Sum.inr b) * g = g * PresentedGroup.of (Sum.inr b) from
    by simpa only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq] using h).symm
theorem mk_inr_eq (R : List (FreeGroup α)) (S : List (FreeGroup β))
    (c : FreeGroup α → FreeGroup β) (w : FreeGroup β) :
    FreeGroup.lift (fun b => PresentedGroup.of (rels := relSet (combinedRelations R S c))
      (Sum.inr b)) w =
      PresentedGroup.mk (relSet (combinedRelations R S c)) (FreeGroup.map Sum.inr w) := by
  have h : FreeGroup.lift (fun b => PresentedGroup.of
      (rels := relSet (combinedRelations R S c)) (Sum.inr b)) =
      (PresentedGroup.mk _).comp (FreeGroup.map Sum.inr) := by
    apply FreeGroup.ext_hom
    intro b
    simp [PresentedGroup.of]
  exact DFunLike.congr_fun h w
noncomputable def kernelMap (R : List (FreeGroup α)) (S : List (FreeGroup β))
    (c : FreeGroup α → FreeGroup β) : PresentedGroup (relSet S) →* Combined R S c :=
  PresentedGroup.toGroup (f := fun b => PresentedGroup.of (Sum.inr b)) (by
    intro s hs
    rw [mk_inr_eq]
    exact combined_kernel_relation R S c s hs)
@[simp] theorem kernelMap_of (R : List (FreeGroup α)) (S : List (FreeGroup β))
    (c : FreeGroup α → FreeGroup β) (b : β) :
    kernelMap R S c (PresentedGroup.of b) = PresentedGroup.of (Sum.inr b) := by
  simp [kernelMap]
theorem kernelMap_range_central (R : List (FreeGroup α)) (S : List (FreeGroup β))
    (c : FreeGroup α → FreeGroup β) :
    (kernelMap R S c).range ≤ Subgroup.center (Combined R S c) := by
  rintro _ ⟨z, rfl⟩
  change z ∈ (Subgroup.center (Combined R S c)).comap (kernelMap R S c)
  apply PresentedGroup.generated_by
  intro b
  change kernelMap R S c (PresentedGroup.of b) ∈ Subgroup.center (Combined R S c)
  rw [kernelMap_of]
  exact combined_generator_central R S c b
instance kernelMap_range_normal (R : List (FreeGroup α)) (S : List (FreeGroup β))
    (c : FreeGroup α → FreeGroup β) : (kernelMap R S c).range.Normal where
  conj_mem := by
    intro a ha g
    have h := Subgroup.mem_center_iff.mp (kernelMap_range_central R S c ha) g
    simpa only [h, mul_assoc, mul_inv_cancel, mul_one] using ha
end Kourovka.MetabelianEnumeration.CentralExtension


