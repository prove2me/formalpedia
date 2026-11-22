-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.ordered_insert_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:06:09.388175+00:00
-- url     : https://prove2.me/submissions/e1196ff0-69f4-4f78-84ee-0f41c7907218

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_ordered_insert
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hshort : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p : Fin a) (v : Lattice k) (i : Fin k) (hv : v ∈ B) (hvi : lower v i ∈ B) :
    conjugate (A p) (orderedWord t v * (t i)⁻¹) =
      conjugate (A p) (orderedWord t (lower v i)) := by
  have hi := ordered_insert A t designated B hB ht hshort p (lower v i) i hvi
    (by simpa using hv)
  rw [raise_lower] at hi
  calc
    conjugate (A p) (orderedWord t v * (t i)⁻¹) =
        conjugate (conjugate (A p) (orderedWord t v)) (t i)⁻¹ := conjugate_mul _ _ _
    _ = conjugate (conjugate (A p) (orderedWord t (lower v i) * t i)) (t i)⁻¹ := by
      rw [hi]
    _ = conjugate (A p) (orderedWord t (lower v i)) := by
      rw [← conjugate_mul]
      simp
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
