-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.normalClosure_abelian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:07:13.977096+00:00
-- url     : https://prove2.me/submissions/4fcbf284-179a-4457-8dea-aefc8a8b918a

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_eq_self
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_ordered_insert
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_ordered_insert_inv
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_closure_mem
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_mem_normalizer_of_conjugate
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hshort : ∀ p q v, Commute (A p) (conjugate (A q) (orderedWord t v)))
    (hgen : Subgroup.closure (Set.range t ∪ Set.range A) = ⊤) :
    ∀ x ∈ Subgroup.normalClosure (Set.range A),
      ∀ y ∈ Subgroup.normalClosure (Set.range A), Commute x y := by
  let S := OrderedOrbit A t
  let H := Subgroup.closure S
  have hsolid : Solid (Set.univ : Set (Lattice k)) := fun _ _ _ _ => trivial
  have hs : ∀ p q v, v ∈ (Set.univ : Set (Lattice k)) →
      Commute (A p) (conjugate (A q) (orderedWord t v)) := fun p q v _ => hshort p q v
  have hT : ∀ i, t i ∈ H.normalizer := by
    intro i
    apply mem_normalizer_of_conjugate
    · apply conjugate_closure_mem
      rintro x ⟨p, v, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨p, raise v i, ?_⟩
      rw [← conjugate_mul]
      exact ordered_insert A t designated Set.univ hsolid ht hs p v i trivial trivial
    · apply conjugate_closure_mem
      rintro x ⟨p, v, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨p, lower v i, ?_⟩
      rw [← conjugate_mul]
      exact ordered_insert_inv A t designated Set.univ hsolid ht hs p v i trivial trivial
  have hAN : ∀ p, A p ∈ H.normalizer := by
    intro p
    apply mem_normalizer_of_conjugate
    · apply conjugate_closure_mem
      rintro x ⟨q, v, rfl⟩
      rw [conjugate_eq_self (hshort p q v)]
      exact Subgroup.subset_closure ⟨q, v, rfl⟩
    · apply conjugate_closure_mem
      rintro x ⟨q, v, rfl⟩
      rw [conjugate_eq_self (hshort p q v).inv_left]
      exact Subgroup.subset_closure ⟨q, v, rfl⟩
  have hn : H.normalizer = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    rintro x (⟨i, rfl⟩ | ⟨p, rfl⟩)
    · exact hT i
    · exact hAN p
  letI : H.Normal := Subgroup.normalizer_eq_top_iff.mp hn
  have hA : Set.range A ⊆ H := by
    rintro x ⟨p, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨p, 0, ?_⟩
    simp [orderedWord]
  have hNH : Subgroup.normalClosure (Set.range A) ≤ H :=
    Subgroup.normalClosure_le_normal hA
  have hHC : H ≤ Subgroup.centralizer (Set.range A) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨q, v, rfl⟩ p ⟨p, rfl⟩
    exact (hshort p q v).eq
  have hAC : Set.range A ⊆ Subgroup.centralizer (H : Set G) := by
    rintro x ⟨p, rfl⟩ y hy
    exact (hHC hy (A p) ⟨p, rfl⟩).symm
  have hNC : Subgroup.normalClosure (Set.range A) ≤ Subgroup.centralizer (H : Set G) :=
    Subgroup.normalClosure_le_normal hAC
  intro x hx y hy
  exact (hNC hx y (hNH hy)).symm
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
